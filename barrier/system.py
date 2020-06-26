"""
Representation of a dynamical system.

We represent an Ordinary Differential Equations with non-linear
dynamic, transcendental functions, and inputs.
"""

try:
    from StringIO import StringIO
except ImportError:
    from io import StringIO

from functools import reduce

import pysmt
from pysmt.shortcuts import *
from pysmt.typing import REAL

from pysmt.shortcuts import *
from pysmt.shortcuts import *



class MalformedSystem(Exception):
    pass

class DynSystem(object):

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

        inverse_odes = {}
        for var, ode_expr in self._odes.items():
            inverse_odes[var] = Minus(Real(0), ode_expr)

        inverse = DynSystem(self._states,
                            self._inputs,
                            self._disturbances,
                            inverse_odes,
                            self._dist_constraints,
                            False)
        return inverse

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
            raise Exeption("Not a state var!")
        else:
            return self._odes[var]

    def get_odes(self):
        odes = {}
        for x in self._states:
            odes[x] = self._odes[x]
        return odes

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
            # A real type term
            elif expr.is_symbol():
                return True
            # Not real type term, not a symbol
            elif (expr.is_plus() or
                  expr.is_minus() or
                  expr.is_times() or
                  expr.is_pow() or
                  expr.is_div()):
                return True
            # A polynomial
            else:
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
                   self._dist_constraints.values(), True)

        )



