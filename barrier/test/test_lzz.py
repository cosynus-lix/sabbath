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
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals,
    GE, GT, LT, LE
)
from pysmt.logics import QF_NRA

from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.lzz.lzz import is_p_invar, lzz

from barrier.lzz.dnf import DNFConverter


class TestLzz(TestCase):

    def test_lzz_pred(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]
        # der(x) = -2y, der(y) = x^2
        dyn_sys = DynSystem([x, y], [], [],
                        {x : -Fraction(2,2) * y, y : x * x},
                        {})

        init = And(Fraction(-1,1) <= x,
                   x <= Fraction(1,2),
                   Fraction(-1, 2) <= y,
                   x <= Fraction(-3,5))
        h = GE(-x - y * y, Real(0))
        p = GE(-x * y + y * y, Real(0))

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = is_p_invar(solver, p, dyn_sys, init, h)

        self.assertTrue(is_invar)

    def test_lzz(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]
        # der(x) = -2y, der(y) = x^2
        dyn_sys = DynSystem([x, y], [], [],
                        {x : -Fraction(2,2) * y, y : x * x},
                        {})
        init = GE(x + y, Real(0))

        # x >= -1 or y > -1/2
        candidate = Or(GE(x, Real(Fraction(-1,1))),
                       GT(y, Real(Fraction(-1,2))))

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = lzz(solver, candidate, dyn_sys, init, TRUE())

        self.assertTrue(is_invar)


    def test_dnf(self):
        def _test_dnf(forig):
            c = DNFConverter()
            f1 = c.get_dnf(forig)
            self.assertTrue(is_valid(Iff(forig, f1)))

        x, y = [Symbol(var, REAL) for var in ["x","y"]]

        p1 = x + y > 0
        p2 = x > 0
        p3 = y >= 0

        _test_dnf(And(Or(p1,p2), Or(p1,p3), Or(p2)))
