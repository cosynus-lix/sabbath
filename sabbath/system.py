"""
Representation of a dynamical system.

We represent an Ordinary Differential Equations with non-linear
dynamic, transcendental functions, and inputs.
"""

try:
    from StringIO import StringIO
except ImportError:
    from io import StringIO

from collections import namedtuple

from functools import reduce


import pysmt
from pysmt.shortcuts import *
from pysmt.typing import REAL

from sabbath.lie import get_inverse_odes, Derivator
from sabbath.formula_utils import FormulaHelper


from sabbath.ts import TS

from sabbath.lyapunov.la_smt import *

class MalformedSystem(Exception):
    pass

def matrix_times_vect_tmp(vect, matrix):
  """
  matrix x vect, where matrix is [m x n] vect is [n x 1], .
  Result is the dot product, [m x 1] vector.

  vect and matrix should contain Real numbers (from pysmt)
  """
  res = []
  for row_index in range(len(matrix)):
    assert(len(matrix[row_index]) == len(vect))

    index_term = Real(0)
    for column_index in range(len(vect)):
      num = matrix[row_index][column_index]
      coefficient = num
      index_term = index_term + Times(vect[column_index], coefficient)
    res.append(simplify(index_term))
  return res


class DynSystem(object):

    @staticmethod
    def get_dyn_sys_affine_description(A, b, PRECISION = 16):
        """
        Construct the dynamical system for der(x) = Ax + b
        """
        states = [Symbol("x_%d" % i, REAL) for i in range(len(A))]

        # dictionary from variable to the ODE right-hand side
        ode_map = {}
        for i in range(len(A)):
            ode_i = Real(0)
            row_i = A[i]
            for j in range(len(row_i)):
                row_i_smt = Real(myround(row_i[j], PRECISION))

                ode_i = ode_i + Times(row_i_smt, states[j])

            ode_map[states[i]] = ode_i + Real(myround(b[i], PRECISION))

        return DynSystem(states, [], [], ode_map, {})

    @staticmethod
    def get_from_matrix(states, A, B):
        """
        Creates a system out of a A and B matrix from sympy
        """
        derivator = Derivator({})

        A_smt = []
        assert (len(states) == A.shape[0])
        for i in range(A.shape[0]):
            vect = []
            for j in range(A.shape[1]):
                elem = A[i,j]
                vect.append(derivator._get_pysmt_expr(elem))
            A_smt.append(vect)

        odes_vec = matrix_times_vect_tmp(states,A_smt)
        if not (B is None):
            assert (B.shape[0] == len(A_smt)) # same number of rows
            for j in range(B.shape[0]):
                odes_vec[j] = odes_vec[j] + derivator._get_pysmt_expr(B[j])

        odes = {}
        for j in range(len(odes_vec)):
            odes[states[j]] = odes_vec[j]

        return DynSystem(states, [], [], odes, {}, {})


    def __init__(self, states, inputs, disturbances, odes,
                 dist_constraints, check_malformed = True):
        # The dynamical system should not change after initialization.
        # So, no side effect on it.

        self._states = [s for s in states]
        self._inputs = [i for i in inputs]
        self._disturbances = [d for d in disturbances]
        self._odes = {}
        for var, ode_expr in odes.items():
            self._odes[var] = ode_expr

        self._dist_constraints = {}
        for var, dist_const in dist_constraints.items():
            self._dist_constraints[var] = dist_const

        if (check_malformed and not self.__check_syntax__()):
            raise MalformedSystem

        self._derivator = None

    def __repr__(self):
        output = StringIO()
        self._to_stream(output)
        return output.getvalue()

    def _to_stream(self, stream):
        """
        We assume the system to be syntactically valid
        """

        def _to_stream_vars(var_list, list_name):
            stream.write("%s vars (%d):" % (list_name, len(var_list)))
            for v in var_list:
                stream.write(" %s" % str(v))
            stream.write("\n")

        stream.write("Dynamical System:\n")
        _to_stream_vars(self._states, "State")
        _to_stream_vars(self._inputs, "Input")
        _to_stream_vars(self._disturbances, "Disturbance")

        stream.write("ODEs:\n")
        for s in self._states:
            stream.write("%s' = " % (str(s)))
            stream.write(self._odes[s].serialize())
            stream.write("\n")

        stream.write("Disturbances:\n")
        for s in self._disturbances:
            stream.write("%s = " % (str(s)))
            stream.write(self._dist_constraints[s].serialize())
            stream.write("\n")


    def get_renamed(self, rename):
        """ Returns a copy of the dynamical system with variables
        renamed as renamed_f
        """

        new_odes = {}
        for var, expr in self._odes.items():
            new_odes[rename(var)] = rename(expr)

        new_constraints = {}
        for var, expr in self._dist_constraints.items():
            new_constraints[rename(var)] = rename(expr)

        renamed_sys = DynSystem(list(map(rename, self._states)),
                                list(map(rename, self._inputs)),
                                list(map(rename, self._disturbances)),
                                new_odes,
                                new_constraints,
                                False)
        return renamed_sys

    def get_inverse(self):
        """ Invert the ODE der(x) = f(x) to der(x) = -f(x)
        Create a new dynamical system.
        """
        inverse_odes = get_inverse_odes(self._odes)
        inverse = DynSystem(self._states,
                            self._inputs,
                            self._disturbances,
                            inverse_odes,
                            self._dist_constraints,
                            False)
        return inverse

    def get_rescaled_by_equilibrium_point(self):
        """ Works on linear systems.

        - Finds the equilibrium points of the system
        - Computes the rescaled linear system


        x' = Ax + b
        Equilibrium point e such that Ax + b = e

        Change of coordinates to z = x - e, so x = z + e

        So, x' = Ax + b
            (z+e)' = A(z+e) + b
            z' = Az + Ae + b
            z' = Az

        If we have a f(z), we get a f'(x) = f(z + e)

        """

        assert (self.is_linear())
        assert (len(self._inputs) == 0)
        assert (len(self._disturbances) == 0)
        assert (len(self._dist_constraints) == 0)

        # find equlibrium point(s)
        solutions = self.get_derivator().get_all_solutions_linear_system(self._odes.values(),
                                                                         self._states)
        rescaled_systems = []
        for solution in solutions:
            rescaled_states = []
            rename_map_body = {}
            z2x = {}
            new_odes = {}
            for x in self._states:
                z = FormulaHelper.get_fresh_var_name(get_env().formula_manager,
                                                     x.symbol_name(),
                                                     x.symbol_type())
                rescaled_states.append(z)
                # Rename x to z (i.e., we susbstitute x with z + e)
                rename_map_body[x] = z + solution[x]
                # Rename z to x (i.e., we substitute z with x - e
                z2x[z] = x - solution[x]

            for x,z in zip(self._states, rescaled_states):
                new_odes[z] = substitute(self.get_ode(x), rename_map_body)

            rescaled_system = DynSystem(rescaled_states,
                                        [],
                                        [],
                                        new_odes,
                                        {},
                                        False)
            rescaled_systems.append((rescaled_system, solution, z2x))

        return rescaled_systems

    def get_derivator(self, pysmt2sympy= None, sympy2pysmt = None):
        """ Return the derivator object for the
        dynamical system.
        """

        if self._derivator is None:
            derivator_vars = self._states
            assert(len(self._disturbances) == 0)

            vector_field = {}
            for var, ode in self._odes.items():
                vector_field[var] = ode

            derivator = Derivator(vector_field, pysmt2sympy, sympy2pysmt)
            self._derivator = derivator

        return self._derivator

    def states(self):
        for x in self._states: yield x

    def inputs(self):
        for x in self._inputs: yield x

    def disturbances(self):
        for x in self._disturbances: yield x

    def odes(self):
        for x in self._odes: yield x

    def dist_constraints(self):
        for x in self._dist_constraints: yield x

    def get_ode(self, var):
        if var not in self._states:
            raise Exception("Not a state var!")
        else:
            return self._odes[var]

    def get_odes(self):
        odes = {}
        for x in self._states:
            odes[x] = self._odes[x]
        return odes

    def is_linear(self):
        """ Returns true if the system is linear (in all the variables, not only the state ones) """
        for ode in self._odes.values():
            degree = self.get_derivator().get_poly_degree(ode)
            if (degree > 1):
                return False
        return True

    # TODO: add logging to the function
    def __check_syntax__(self):
        """ Returns true only if the system is syntactically correct.

        We require:
        - elements in the variables to be Symbols of REAL type
        - different variables set must be disjoint
        - there must be exactly one ode for each state variable
        - the ODE expression must only contain symbols from the variables
        - the ODE expression must be a term (not a predicate or a formula)
        - there must be exactly one constraint for each distubance
        - the constraints on distubances must contains only the distubance they describe
        - the constraints on the disturbances must be a convex constraint
        """
        def _are_vars_symbols(var_list):
            for v in var_list:
                if not v.is_symbol():
                    return False
                elif v.get_type() != REAL:
                    return False
            return True

        def _are_disjoint(list1, list2):
            return set(list1).isdisjoint(set(list2))

        def _is_expr(expr):
            if (expr.get_type() != REAL):
                return False
            elif expr.is_constant():
                # a real type constant
                return True
            elif expr.is_symbol():
                # a real type expression
                return True
            elif (expr.is_plus() or
                  expr.is_minus() or
                  expr.is_times()):
                # a real type polynomial
                return True
            else:
                # otherwise
                return False

        def _check_ode(ode_expr):
            assert not ode_expr is None

            if not _is_expr(ode_expr):
                return False
            else:
                myset = set(self._states)
                myset.update(self._inputs)
                myset.update(self._disturbances)

                for a in set(ode_expr.get_free_variables()):
                    if a.is_symbol() and (not a in myset):
                        return False
            return True

        def _check_dist(expr):
            if (expr.get_type() != BOOL):
                return False
            else:
                # all vars from disturbances
                for a in set(expr.get_free_variables()):
                    if a.is_symbol() and (not a in self._disturbances):
                        return False
                return True

        return (
            len(self._states) > 0 and
            # no duplicates
            len(self._states) == len(set(self._states)) and
            len(self._inputs) == len(set(self._inputs)) and
            len(self._disturbances) == len(set(self._disturbances)) and
            # all symbols
            _are_vars_symbols(self._states) and
            _are_vars_symbols(self._inputs) and
            _are_vars_symbols(self._disturbances) and
            # disjoints
            _are_disjoint(self._states, self._inputs) and
            _are_disjoint(self._states, self._disturbances) and
            _are_disjoint(self._inputs, self._disturbances) and

            # at least one ode for each x
            reduce(lambda acc, var: acc and var in self._odes,
                   self._states, True) and
            # at most one
            len(self._odes) == len(self._states) and
            # all ode are expr from set vars and ode only term
            reduce(lambda acc, expr: acc and _check_ode(expr),
                   self._odes.values(), True) and

            # at least one expr for each disturbances
            reduce(lambda acc, var: acc and var in self._dist_constraints,
                   self._disturbances, True) and
            # at most one
            len(self._dist_constraints) == len(self._disturbances) and
            # all dist are predicates from set vars
            reduce(lambda acc, expr: acc and _check_dist(expr),
                   self._dist_constraints.values(), True) and

            True
        )


def is_linear_formula(formula):
    """
    Tells if a formula is piecewise affine.
    """
    formula = formula.simplify()
    if formula.is_symbol() or formula.is_real_constant():
        return True
    if formula.is_plus() or formula.is_minus():
        return is_linear_formula(formula.arg(0)) and is_linear_formula(formula.arg(1))
    elif formula.is_times() == 15:
        if formula.arg(0).is_symbol():
            if formula.arg(1).is_real_constant():
                return True
        if formula.arg(0).is_real_constant():
            return is_linear_formula(formula.arg(1))
    return False

class HybridAutomaton(object):
    """
    Explicit hybrid automata representation (locations and edges are explicit).
    """

    Location = namedtuple("Location", "invar vector_field")
    Edge = namedtuple("Edge", "dst trans")

    def __init__(self, disc_vars, cont_vars, init, locations, edges):
        # Discrete variables of the automaton
        self._disc_vars = list(disc_vars)
        self._cont_vars = list(cont_vars)

        # Initial condition
        self._init = {}
        for (loc_name, data) in init.items():
            self._init[loc_name] = data

        # List of locations
        self._locations = {}
        for (loc_name, data) in locations.items():
            self._locations[loc_name] = data

        # Adjacency lists for edges
        self._edges = {}
        for loc_name, data  in edges.items():
            dst_list = [l for l in data]
            self._edges[loc_name] = dst_list

    def is_pred_cont(self, pred):
        for v in pred.get_free_variables():
            if v in self._cont_vars:
                return True
        return False

    # def to_str(self):
    #     print(self._disc_vars)
    #     print(self._cont_vars)
    #     print("Init:")
    #     for k,v in self._init.items():
    #         print("  %s: %s" % (k,v))
    #     print("Locations")
    #     for k,v in self._locations.items():
    #         print("  %s: %s" % (k, v.invar))

    def is_piecewise_affine(self):
        """
        Tells if the hybrid automaton is piecewise affine.
        """
        linearity_values = []
        for index_mode in range(len(self._locations)):
            for ode in self._locations[f"{index_mode}"][1].get_odes().values():
                linearity_values.append(is_linear_formula(ode))
            constraint = self._locations[f"{index_mode}"][0]
            switch = Plus(constraint.arg(0), Times(constraint.arg(1), Real(-1)))
            linearity_values.append( is_linear_formula(switch))
        
        return all(linearity_values)

HaProp = namedtuple("HaProp", "global_prop prop_by_loc")
HaVerProblem = namedtuple("HaVerProblem", "name ha prop predicates")

