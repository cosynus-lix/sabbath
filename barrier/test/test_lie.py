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

from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.lie import get_lie, Derivator, Pysmt2Sympy, Sympy2Pysmt


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
            lie = get_lie(expr, sys)
            eq = Equals(lie, expected_lie)

            # print("\nAAA")
            # print(sys)
            # print("Lie 0: " + str(expr))
            # print("Lie 1: " + str(lie))
            # print("Lie 2: " + str(get_lie(lie, sys)))
            # print("Lie 3: " + str(get_lie(get_lie(lie, sys), sys)))


            same = is_valid(eq)
            self.assertTrue(same)

    def test_rank(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]

        vars_list = [x,y]
        expr = - x * y + y * y
        vector_field = {x : -Fraction(2,2) * y, y : x * x}

        der = Derivator()
        rank = der.get_lie_rank(vars_list, expr, vector_field)

        self.assertTrue(rank == 2)
