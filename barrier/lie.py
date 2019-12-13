"""
Compute the lie derivative of a dynamical system.
"""

from fractions import Fraction
from functools import reduce

from pysmt.shortcuts import (
    Real, Symbol,
    Plus, Times, Pow
)
from pysmt.walkers import DagWalker
from pysmt.typing import REAL

from sympy import diff
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
from sympy.polys.polytools import reduced

from barrier.system import DynSystem


def get_lie(expr, dyn_sys):
    """ Get the lie derivative of the expression with respect to the
    dynamical system dyn_system.

    Returns an expression representing the lie derivative.
    """

    der = Derivator()
    lie_der = der.get_lie_der(dyn_sys.states(), expr, dyn_sys.get_odes())

    return lie_der

def get_lie_rank(self, expr, dyn_sys):
    """ Get the rank of expr and the vector field of dyn_sys
    """

    der = Derivator()
    rank = der.get_lie_rank(dyn_sys.states(), expr, dyn_sys.get_odes())

    return rank

class Derivator(object):
    """
    Simple wrapper between pysmt polynomials and sympy expressions.
    """

    def __init__(self):
        self.pysmt2sympy = Pysmt2Sympy()
        self.sympy2pysmt = Sympy2Pysmt()

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

        sympy_lie = diff(sympy_expr, sympy_x) * sympy_ode
        pysmt_lie = self._get_pysmt_expr(sympy_lie)

        return pysmt_lie

    def _get_lie_der(self, vars_list, expr, vector_field):
        """
        Actual computation of the Lie derivative in SyPy
        """
        lie_der = 0

        for var in vars_list:
            lie_var = Mul_sympy(diff(expr, var), vector_field[var])
            lie_der = Add_sympy(lie_der, lie_var)

        return lie_der

    def _get_sympy_problem(self, vars_list, expr, vector_field):
        _vector_field = {}
        _vars_list = []
        for var in vars_list:
            _var = self._get_sympy_expr(var)
            _vars_list.append(_var)
            _vector_field[_var] = self._get_sympy_expr(vector_field[var])
        _expr = self._get_sympy_expr(expr)

        return (_vars_list, _expr, _vector_field)

    def get_lie_der(self, vars_list, expr, vector_field):
        """
        Takes as input a set of (pysmt) variables, an (pysmt) expression of a
        predicate, and dynamical_system.
        """

        (_vars_list, _expr, _vector_field) = self._get_sympy_problem(vars_list, expr, vector_field)

        # Compute the Lie derivative in SymPy
        _lie_der = self._get_lie_der(_vars_list, _expr, _vector_field)
        lie_der = self._get_pysmt_expr(_lie_der)

        return lie_der

    def get_lie_rank(self, vars_list, expr, vector_field):
        """
        Compute the rank of the expression p and the vector field f.

        The rank is defined in the paper:

        Computing Semi-algebraic Invariants for Polynomial Dynamical Systems
        Liu, Zhan, Zhao, EMSOFT11

        The computation finds the N such that Lp,f^{N+1} is in the ideal <Lp,f^0, Lp,f^1, ..., Lp,f^{N}>
        (where p is the polynomial expression, and Lp,f(i) is the i-th Lie derivative of p wrt f.

        Note that such N exists, due to the ascending chain condition of ideals.
        """

        def _get_lie_rank(vars_list, expr, vector_field):
            """
            Implement the algorithm directly in sympy.x
            """
            n = -1
            lie_n = expr
            lies = [expr]

            fix_point = False

            while (not fix_point):
                n = n + 1

                bases = groebner(lies, vars_list, order='lex')

                lie_n = self._get_lie_der(vars_list, lie_n, vector_field)

                _, f = reduced(lie_n, bases, wrt=vars_list)

                fix_point = True
                for var in vars_list:
                    if (f.has(var)):
                        # Cannot write lie_n with the bases!
                        fix_point = False
                        lies.append(lie_n)
                        break

            return n

        (_vars_list, _expr, _vector_field) = self._get_sympy_problem(vars_list, expr, vector_field)

        rank = _get_lie_rank(_vars_list, _expr, _vector_field)

        return rank


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
        return formula.constant_value()

    def walk_int_constant(self, formula, args, **kwargs):
        return formula.constant_value()

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


class Sympy2Pysmt(object):
    """
    Not super robust --- just do what we need to do now
    """
    def __init__(self):
        self.cache = {}

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

        elif (isinstance(sympy_expr, Mul_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))
            return Times(pysmt_args)
        elif (isinstance(sympy_expr, Add_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))
            return Plus(pysmt_args)
        elif (isinstance(sympy_expr, Pow_sympy)):
            pysmt_args = list(map(lambda x: self.walk(x), sympy_expr.args))

            # 2nd argument from pow must be constant

            print(pysmt_args)

            assert (pysmt_args[1].is_constant())

            return Pow(pysmt_args[0], pysmt_args[1])
        elif (isinstance(sympy_expr, Fraction)):
            return Real(sympy_expr)
        else:
            raise Exception("Found unkonwn operator (%s) in %s" % (type(sympy_expr),
                                                                   str(sympy_expr)))
