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
    is_valid,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals
)

from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.lie import get_lie, Derivator, Pysmt2Sympy, Sympy2Pysmt


class TestLie(TestCase):

    def test_conversion(self):
        def convert(pysmt_formula):
            sympyformula = smt2sym.walk(pysmt_formula)
            pysmt_formula_back = sym2smt.walk(sympyformula)
            return pysmt_formula_back is pysmt_formula_back

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

        for s in exprs:
            self.assertTrue(convert(s))


    def test_lie(self):
        x1, x2, x3 = [Symbol("x%s" % (i+1), REAL) for i in range(3)]

        sys = DynSystem([x1, x2], [], [],
                        {
                            x1 :  -x2,
                            x2 : x1
                        },
                        {})

        # TODO: add more test cases
        exprs = [(x1 + 3 * x2, (- (x2)) + 3 * x1)]

        for (expr, expected_lie) in exprs:
            lie = get_lie(expr, sys)
            eq = Equals(lie, expected_lie)
            same = is_valid(eq)
            self.assertTrue(same)


