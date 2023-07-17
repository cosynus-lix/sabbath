""" Test the system """


import logging
import unittest
import os
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    is_valid, get_model,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals
)

from sabbath.test import TestCase
from sabbath.system import DynSystem
from sabbath.lie import Derivator, Pysmt2Sympy, Sympy2Pysmt


class TestLie(TestCase):

    def test_conversion(self):
        def convert(pysmt_formula, side_conditions):
            sympyformula = smt2sym.walk(pysmt_formula)
            pysmt_formula_back = sym2smt.walk(sympyformula)

            print("Model %s:\n%s\n"  % (
                str(Equals(pysmt_formula, Real(0))),
                str(get_model(Equals(pysmt_formula, Real(0))))
            ))
            print("Model %s:\n%s\n"  % (
                str(Equals(pysmt_formula_back, Real(0))),
                str(get_model(Equals(pysmt_formula_back, Real(0))))
            ))

            if (pysmt_formula_back is pysmt_formula):
                return True
            else:
                print("---")
                print(pysmt_formula.serialize())
                print(pysmt_formula_back.serialize())

                if pysmt_formula in side_conditions:
                    sc = side_conditions[pysmt_formula]
                else:
                    sc = TRUE()

                f1 = And(sc, Equals(pysmt_formula, Real(0)))
                f2 = And(sc, Equals(pysmt_formula_back, Real(0)))

                return is_valid(Iff(f1,f2))


        smt2sym = Pysmt2Sympy()
        sym2smt = Sympy2Pysmt()

        x1, x2, x3 = [Symbol("x%s" % (i+1), REAL) for i in range(3)]

        p = Symbol("p", INT)
        from pysmt.shortcuts import Pow

        exprs = [x1, x2, x3,
                 x1 + x2,
                 3 + x1,
                 x1 + x2 + x3,
                 3 * x1,
                 x1 * x2,
                 Pow(x1, Real(2.0)),
                 Pow(x1, Real(2.0)) * Pow(x1, Real(2.0))
                 -3,
                 Real(Fraction(-2, -3)),
                 Pow((x1 * x2), Real(2)),
                 x1 / x2 + Real(Fraction(-2, -3))]

        # Undef behavior when x2 = 0
        expr = x1 / x2 + Real(Fraction(-2, -3))
        sc = {expr : Not(Equals(Real(0),x2))}

        for s in exprs:
            self.assertTrue(convert(s, sc))


    def test_lie(self):
        x1, x2, x3 = [Symbol("x%s" % (i+1), REAL) for i in range(3)]

        sys1 = DynSystem([x1, x2], [], [],
                         {
                            x1 :  -x2,
                            x2 : x1
                         },
                         {})

        sys2 = DynSystem([x1, x2], [], [],
                         {
                            x1 :  -Fraction(2,1) * x2,
                            x2 : x1
                         },
                         {})

        # TODO: add more test cases
        exprs = [
            (sys1, x1 + 3 * x2, (- (x2)) + 3 * x1),
            (sys2, x1 + 1, Real(Fraction(-2,1)) * x2)
        ]


        for (sys, expr, expected_lie) in exprs:
            derivator = sys.get_derivator()
            lie = derivator.get_lie_der(expr)
            eq = Equals(lie, expected_lie)
            same = is_valid(eq)
            self.assertTrue(same)

    def _app_rank(self, expr, vector_field, expected):

        # print("Computing rank for")
        # print(vector_field)
        # print(expr)

        der = Derivator(vector_field)
        rank = der.get_lie_rank(expr)
        self.assertTrue(rank == expected)


    def test_rank(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]

        vector_field = {x : -Fraction(2,2) * y, y : x * x}
        self._app_rank(- x * y + y * y, vector_field, 2)

        vector_field = {x : -2 * y, y : x * x}
        self._app_rank(x+y*y, vector_field, 2)

        vector_field = { x : x + y - x*x*y - y*y*y,
                         y : x - x*x*x + y - x*y*y}
        self._app_rank(2 - y, vector_field, 2)

        self._app_rank(x * y, {x : Real(1), y : Real(0)}, 1)

        var_names = ["x1","x2","y1","y2","d1","d2","e1","e2","o","t","u0","u1","u2","u3","u4"]
        x1,x2,y1,y2,d1,d2,e1,e2,o,t,u0,u1,u2,u3,u4 = [Symbol(var,REAL) for var in var_names]
        vector_field = {x1 : d1,
                        x2 : d2,
                        y1 : e1,
                        y2 : e2,
                        d1 : -o*d1,
                        d2 : o*d2,
                        e1 : -t*e2,
                        e2 : t*e2,
        }
        self._app_rank(u1*x1 + u2*x2 + u3*d1 + u4*d2 + u0,
                       vector_field, 2)
        self._app_rank(u1 * d1 * d1 + u2 * d2 * d2 + u0,
                       vector_field, 2)

        self._app_rank(-x - y*y, {x : -2 * y, y : x*x}, 2)


    def test_rank_fractions(self):
        r05 = Fraction(1,2)
        r0 = Real(0)
        r2 = Real(2)
        r1 = Real(1)

        var_names = ["x1","x2","v1","v2",
                     "k1","k2","m1","m2",
                     "u1","u8","u10"]
        x1,x2,v1,v2,k1,k2,m1,m2,u1,u8,u10 = [Symbol(var,REAL) for var in var_names]
        vector_field = {x1: v1,
                        x2: v2,
                        v1: ((-r1 * ((k1 / m1) * x1)) - ((k2 / m1) * (x1 - x2))),
                        v2: (-r1 * ((k2 / m2) * (x2 - x1))),
                        u1: r0,
                        u8: r0,
                        u10: r0}

        expr = - (
            ((v2 * u8 * v1) + ((x1 * x2 * k2 * ((m1 * u8) - (r2 * m2 * u10))) / (m2 * m1))) +
            (u10 * v1 * v1) +
            u1 +
            ((r05 * v2 * v2 * ((((k1 * m2 * u8) - (k2 * m1 * u8)) + (m2 * k2 * u8)) + (r2 * m2 * u10 * k2))) / (k2 * m1)) +
            ((r05 * x1 * x1 * (((r2 * k1 * m2 * u10) - (k2 * m1 * u8)) + (r2 * m2 * u10 * k2))) / (m2 * m1)) +
            ((r05 * x2 * x2 * (((k1 * m2 * u8) - (k2 * m1 * u8)) + (r2 * m2 * u10 * k2))) / (m2 * m1))
        )

        self._app_rank(expr, vector_field, 1)


    def test_rank_constant_lie(self):
        x1,u1 = [Symbol(v, REAL) for v in ["x1","u1"]]
        self._app_rank(u1 - Real(20), {x1 : x1}, 1)


    def test_get_remainders_list(self):
        def aux(poly, f, vars_list):
            dyn_sys = DynSystem(vars_list, [], [], f, {})
            derivator = dyn_sys.get_derivator()
            return derivator.get_remainders_list(poly)

        vars_list_str = ["x","y"]
        vars_map = {var : Symbol(var, REAL) for var in vars_list_str}
        vars_list = [vars_map[s] for s in vars_list_str]
        x = vars_map["x"]
        y = vars_map["y"]

        tc = [
            (x, {x : x*x + y, y : 2*y*y}, vars_list, [x,y]),
            (x*x, {x : x*x + y, y : 2*y*y}, vars_list, [(x * x), (2.0 * x * y), (2.0 * (y * y))]),
            (x+y, {x : x*x + y, y : 2*y*y}, vars_list, [(x + y), (y + (3.0 * (y * y))), (Fraction(2,3) * y)]),
            (x*y, {x : x*x + y, y : 2*y*y}, vars_list, [(x * y), (y*y)]),
            (x + Real(1), {x : -Fraction(2,1) * y, y : x * x}, [x,y], [1 + x, -2 * y, Real(-2)])
        ]

        for t in tc:
            res = aux(t[0],t[1],t[2])
            for p1,p2 in zip(res, t[3]):
                self.assertTrue(is_valid(Equals(p1,p2)))
