"""
Compute the lie derivative of a dynamical system.
"""

from fractions import Fraction
from functools import reduce
import logging

from pysmt.shortcuts import (
    Real, Symbol, Minus,
    Plus, Times, Pow, Div,
    get_free_variables
)
from pysmt.walkers import DagWalker
from pysmt.typing import REAL

from sympy import diff, sympify
from sympy import symbols as sympy_symbols

from sympy import (
    diff as sympy_diff,
    symbols as sympy_symbols,
    Symbol as Symbol_sympy,
    Number as Number_sympy,
    Mul as Mul_sympy,
    Add as Add_sympy,
    Pow as Pow_sympy,
    Rational as Rational_sympy,
    Integer as Integer_sympy,
)

from sympy import groebner
from sympy.polys.domains import RR,ZZ
from sympy.polys.polytools import reduced


def get_inverse_odes(_odes):
    inverse_odes = {}
    for var, ode_expr in _odes.items():
        inverse_odes[var] = Minus(Real(0), ode_expr)
    return inverse_odes

class Derivator(object):
    """
    Implements lie derivaties and rank computation.

    Now uses sympy as computer algebra system.
    """

    def __init__(self, vector_field, pysmt2sympy= None, sympy2pysmt = None):
        self.vector_field = vector_field

        self.cont_vars = set([v for v in vector_field.keys()])
        # parameters of the vector field that do not have a derivative
        self.vector_field_params = (
            reduce(lambda params,expr: self._add_param(params,expr),
                   self.vector_field.values(), set())
        )

        self.pysmt2sympy = Pysmt2Sympy() if pysmt2sympy is None else pysmt2sympy
        self.sympy2pysmt = Sympy2Pysmt() if sympy2pysmt is None else sympy2pysmt

        # memoization for the rank computation
        self._rank_memo = {}

    def _add_param(self, params, expr):
        for fv in get_free_variables(expr):
            if not fv in self.cont_vars:
                params.add(fv)
        return params

    def _get_sympy_expr(self, pysmt_expr):
        return self.pysmt2sympy.walk(pysmt_expr)

    def _get_pysmt_expr(self, sympy_expr):
        return self.sympy2pysmt.walk(sympy_expr)

    def _get_lie_var(self, pysmt_expr, dyn_sys, x):
        """ Get the part of the lie derivative for var.

        It is the product of the partial derivative of expr wrt. the variable x and
        the derivative of x in dyn_sys.
        """
        sympy_x = self._get_sympy_expr(x)
        sympy_expr = self._get_sympy_expr(pysmt_expr)
        sympy_ode = self._get_sympy_expr(dyn_sys.get_ode(x))

        sympy_lie = sympy_diff(sympy_expr, sympy_x) * sympy_ode
        pysmt_lie = self._get_pysmt_expr(sympy_lie)

        return pysmt_lie

    @staticmethod
    def _get_lie_der_sympy(expr_sympy, vector_field_sympy):
        """
        Actual computation of the Lie derivative in SyPy
        """
        lie_der = 0

        for var, rhs_ode in vector_field_sympy.items():
            diff_expr = sympy_diff(expr_sympy, var)
            lie_var = Mul_sympy(diff_expr, rhs_ode)
            lie_der = Add_sympy(lie_der, lie_var)
        return lie_der

    def _get_sympy_problem(self, expr):
        _vector_field = {}
        _params = [str(self._get_sympy_expr(var)) for var in self.vector_field_params]
        _domain = 'ZZ[%s]' % (",".join(_params))
        _cont_vars = tuple([self._get_sympy_expr(var) for var in self.vector_field.keys()])
        for var, vector_field_expr in self.vector_field.items():
            _var = self._get_sympy_expr(var)
            _sympy_der = self._get_sympy_expr(vector_field_expr)
            # print("here")
            # print(_sympy_der)
            # print(_cont_vars)
            # print(_params)
            _vector_field[_var] = _sympy_der #.as_poly(_cont_vars) # , domain=_domain
        _expr = self._get_sympy_expr(expr)   #.as_poly(_cont_vars) #, domain=_domain

        return (_expr, _vector_field, _domain)

    def get_inverse(self):
        return Derivator(get_inverse_odes(self.vector_field),
                         self.pysmt2sympy,
                         self.sympy2pysmt)

    def get_lie_der(self, expr):
        """
        Takes as input a set of (pysmt) variables, an (pysmt) expression of a
        predicate, and dynamical_system.
        """

        (_expr, _vector_field, _domain) = self._get_sympy_problem(expr)
        # Compute the Lie derivative in SymPy
        _lie_der = Derivator._get_lie_der_sympy(_expr, _vector_field)
        lie_der = self._get_pysmt_expr(_lie_der)

        return lie_der

    def get_lie_rank(self, expr):
        """
        Compute the rank of the expression p and the vector field f.

        The rank is defined in the paper:

        Computing Semi-algebraic Invariants for Polynomial Dynamical Systems
        Liu, Zhan, Zhao, EMSOFT11

        The computation finds the N such that Lp,f^{N+1} is in the ideal <Lp,f^0, Lp,f^1, ..., Lp,f^{N}>
        (where p is the polynomial expression, and Lp,f(i) is the i-th Lie derivative of p wrt f.

        Note that such N exists, due to the ascending chain condition of ideals.
        """

        def _get_lie_rank_sympy(expr_sympy, vector_field_sympy, domain):
            """
            Implement the algorithm directly in sympy.x
            """
            n = -1
            lie_n = expr_sympy
            lies = [expr_sympy]

            fix_point = False
            vars_list = [v for v in vector_field_sympy.keys()]
            while (not fix_point):
                n = n + 1

                # see https://mattpap.github.io/masters-thesis/html/src/groebner.html#algebraic-relations-in-invariant-theory
                lie_n = Derivator._get_lie_der_sympy(lie_n, vector_field_sympy)

                if (0 == len(lie_n.free_symbols.intersection(vars_list))):
                    # lie derivative has only constants
                    fix_point = True
                    break

                bases = groebner(lies, vars_list, order='lex')
                #bases = groebner(lies, vars_list, order='lex')


                # print(lies)
                # print(vars_list)
                # print(bases)
                # print(lie_n)

                # Reduced is the heavy computation function here.
                coeff, remainder = reduced(lie_n, bases, wrt=vars_list)

                fix_point = True
                if (remainder.expand() != 0):
                    lies.append(lie_n)
                    fix_point = False

            # DEBUG CODE -- verify that lie_n can be expressed using a
            # basis of the previous lie derivatives
            #
            # This is a correctness check for the rank computation
            #
            # logging.debug(coeff)
            # logging.debug(remainder)
            # logging.debug(bases)
            # all_sum = remainder
            # for b, c in zip(bases, coeff):
            #     all_sum += b * c
            # logging.debug(all_sum)
            # assert(all_sum.expand() == lie_n.expand())

            return n

        if (expr in self._rank_memo):
            logging.debug("Rank in cache... " + expr.serialize())
            return self._rank_memo[expr]
        else:
            logging.debug("Computing rank... ")
            # logging.debug("Rank expr: " + expr.serialize())
            # logging.debug("On vector field: " + str(self.vector_field))

            self._add_param(self.vector_field_params, expr)

            _params = [self._get_sympy_expr(v) for v in self.vector_field_params]
            (_expr, _vector_field, _domain) = self._get_sympy_problem(expr)
            rank = _get_lie_rank_sympy(_expr, _vector_field, _domain)
            logging.debug("Computed rank %d" % rank)

            self._rank_memo[expr] = rank
            return rank

# EOC Derivator

class Pysmt2Sympy(DagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def walk_symbol(self, formula, args, **kwargs):
        if (formula.symbol_type() != REAL):
            # only allow to have real variables
            raise NotImplementedError

        sympy_symbol = sympy_symbols(formula.symbol_name())
        return sympy_symbol

    def walk_real_constant(self, formula, args, **kwargs):
        return sympify(formula.constant_value())

    def walk_int_constant(self, formula, args, **kwargs):
        return sympify(formula.constant_value())

    def walk_plus(self, formula, args, **kwargs):
        assert len(args) > 0
        res = None
        for elem in args:
            res = elem if res is None else res + elem
        return res

    def walk_times(self, formula, args, **kwargs):
        assert len(args) > 0
        res = None
        for elem in args:
            res = elem if res is None else res * elem
        return res

    def walk_pow(self, formula, args, **kwargs):
        assert len(args) == 2
        return args[0]**args[1]

    def walk_minus(self, formula, args, **kwargs):
        assert len(args) == 2
        return args[0] - args[1]

    def walk_div(self, formula, args, **kwargs):
        assert len(args) == 2
        return args[0] / args[1]

    def walk_bool_constant(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_constant(self, formula, **kwargs):
        raise NotImplementedError

    def walk_and(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_or(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_not(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_iff(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_implies(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_equals(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_ite(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_le(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_lt(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_forall(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_exists(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_function(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_toreal(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_constant(self, formula, **kwargs):
        raise NotImplementedError

    def walk_bv_and(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_not(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_neg(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_or(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_xor(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_add(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_sub(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_mul(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_udiv(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_urem(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_ult(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_ule(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_extract(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_ror(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_rol(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_sext(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_zext(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_concat(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_lshl(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_lshr(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_ashr(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_comp(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_slt(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_sle(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_sdiv(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_srem(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_length(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_concat(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_contains(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_indexof(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_replace(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_substr(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_prefixof(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_suffixof(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_to_int(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_int_to_str(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_str_charat(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_bv_tonatural(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_array_select(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_array_store(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_array_value(self, formula, args, **kwargs):
        raise NotImplementedError

# EOC Pysmt2Sympy

class Sympy2Pysmt(object):
    """
    Not super robust --- just do what we need to do now
    """
    def __init__(self):
        self.cache = {}

    # True if translate Pow to Pow, otherwise expand the
    # Multiplication
    USE_POW=False

    def walk(self, sympy_expr):
        if sympy_expr in self.cache:
            cached = self.cache[sympy_expr]
            return cached
        else:
            res = self.walk_rec(sympy_expr)
            self.cache[sympy_expr] = res

            return res

    def walk_rec(self, sympy_expr):
        if (isinstance(sympy_expr, Symbol_sympy)):
            # Assume symbol is real
            return Symbol(str(sympy_expr), REAL)
        elif (isinstance(sympy_expr, Number_sympy)):
            # To test for imprecisions

            if isinstance(sympy_expr, Rational_sympy):
                return Real(Fraction(sympy_expr.p, sympy_expr.q))
            elif isinstance(sympy_expr, Integer_sympy):
                return Int(sympy_expr.p)
            else:
                raise Exception("Found unkonwn operator in " + str(sympy_expr))
        elif (isinstance(sympy_expr, Fraction)):
            return Real(sympy_expr)
        elif (isinstance(sympy_expr, Mul_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))
            return Times(pysmt_args)
        elif (isinstance(sympy_expr, Add_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))
            return Plus(pysmt_args)
        elif (isinstance(sympy_expr, Pow_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))

            # 2nd argument from pow must be constant
            assert (pysmt_args[1].is_constant())

            if not Sympy2Pysmt.USE_POW:
              # Alternative version using Times explicitly (mathsat and smtlib do not handle pow)
              if not (pysmt_args[1].is_int_constant()):
                exponent = pysmt_args[1].constant_value()
                exponent = int(exponent)
              else:
                # Try to be lucky
                exp_fraction = Fraction(pysmt_args[1])
                exponent = int(exp_fraction)

              if (exponent == 0):
                # Assume real type
                return Real(1)
              else:
                flip = (exponent < 0)
                if exponent < 0:
                  exponent = - exponent

                res = pysmt_args[0]
                for i in range(exponent-1):
                  res = Times(res, pysmt_args[0])

                if (flip):
                  res = Div(Real(1), res)

                return res
              # End of alternative version
            else:
              return Pow(pysmt_args[0], pysmt_args[1])
        else:
            raise Exception("Found unkonwn operator (%s) in %s" % (type(sympy_expr),
                                                                   str(sympy_expr)))

# EOC Sympy2Pysmt
