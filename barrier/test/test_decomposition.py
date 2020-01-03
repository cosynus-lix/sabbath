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
from barrier.utils import get_range_from_int

from barrier.decomposition.explicit import (
    _get_solver,
    _get_neighbors,
    _set_to_formula,
    get_invar_lazy_set,
    get_invar_lazy,
    dwc,
    dwcl
)


class TestDecomposition(TestCase):

    def _print_abs_states(self, got):
        logger = logging.getLogger(__name__)
        logger.info("RESULT:")

        for abs_state in got:
            abs_state_str = "p(x) := "
            for pred in abs_state:
                abs_state_str += " %s" % pred.serialize()
            logging.info(abs_state_str)

    def _eq_sets(self, got, expected):
        new_exp = set()
        for s in expected:
            new_exp.add(frozenset(s))
        same = got == new_exp

        if not same:
            self._print_abs_states(got)
        return same

    def _eq_wformula(self, got, expected):
        solver = _get_solver()
        formula = _set_to_formula(expected)
        same = solver.is_valid(Iff(got, formula))
        return same

    @unittest.skip("")
    def test_get_neighbors(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]

        r0 = Real(0)
        poly = [x, y]

        tc = [
            # (x<0,y<0) -> [(x=0,y=0),(x<0,y=0),(x=0,y<0)]
            ({x<r0, y<r0},
             [{Equals(x, r0), Equals(y, r0)},
              {x<r0, Equals(y, r0)},
              {Equals(x, r0), y<r0}]),
            # (x=0,y=0) -> [(x<0,y<0),(x<0,y=0),(x<0,y>0),
            #               (x>0,y<0),(x>0,y=0),(x>0,y>0),
            #               (x=0,y<0),(x=0,y>0)]
            ({Equals(x, r0), Equals(y, r0)},
             [{x<r0,y<r0},
              {x<r0,Equals(y,r0)},
              {x<r0,r0<y},
              {r0<x,y<r0},
              {r0<x,Equals(y,r0)},
              {r0<x,r0<y},
              {Equals(x,r0), y<r0},
              {Equals(x,r0),r0<y},
             ]),
            # (x=0,y<0) -> [(x=0,y=0),(x<0,y<0),(x>0,y<0)]
            ({Equals(x, r0), y<r0},
             [{Equals(x, r0), Equals(y, r0)},
              {x<r0, y<r0},
              {r0<x, y<r0}]),
        ]

        for (abs_state, neighbors) in tc:
            res = _get_neighbors([x,y], abs_state)
            res_set = set([frozenset(s) for s in res])
            neighbors_set = set([frozenset(s) for s in neighbors])

            # print("abs state")
            # print(abs_state)
            # print("Obtained")
            # print(res_set)
            # print("Expected")
            # print(neighbors_set)

            self.assertTrue(res_set == neighbors_set)

    @staticmethod
    def get_test_case_1():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(get_range_from_int([x, y], [(1,2),(1,2)]))

        expected_invar = [{x<r0,y<r0},
                          {x<r0,Equals(y,r0)},
                          {x<r0,r0<y},
                          {Equals(x,r0),y<r0},
                          {r0<x,y<r0}]

        return (dyn_sys, TRUE(),[x,y], init, safe,
                expected_invar)

    @staticmethod
    def get_test_case_2():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [],
                            {x : -(y*y), y : x*x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(2,3), (-1,1)])
        safe = Not(get_range_from_int([x, y], [(0,0),(0,0)]))

        expected_invar = [{(0.0 < x),(y < 0.0)},
                          {(r0 < x),Equals(y,r0)},
                          {(r0 < y),(r0 < x)},
                          {(r0 < y),Equals(x,r0)},
                          {(r0 < y),(x < r0)},
                          {Equals(x,r0),(y < r0)},
                          {(x < r0),(y < r0)},
                          {(x < r0),Equals(y,r0)}]

        return (dyn_sys, TRUE(),[x,y], init, safe,
                expected_invar)

    @staticmethod
    def get_test_case_3():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(And(Equals(x,r0),y<r0))
        return (dyn_sys, TRUE(),[x,y], init, safe,[])

    @staticmethod
    def get_test_case_4():
        def _pow(var, degree):
            res = Real(1)
            for i in range(degree):
                res = var * res
            return res

        x1, x2 = [Symbol(var, REAL) for var in ["x1", "x2"]]

        fx1 = 2 * x1 * (x1*x1 - 3) * (4*x1*x1 - 3) * (x1*x1 + 21*x2*x2 - 12)
        f2_rh = (35*_pow(x1,6) +
                 105*_pow(x2,2)*_pow(x1,4) +
                 (-315)*_pow(x1,4) +
                 (-63)*_pow(x2,4)*_pow(x1,2) +
                 378*_pow(x1,2)+
                 27*_pow(x2,6)+
                 (-189)*_pow(x2,4)+
                 378*_pow(x2,2)-
                 216)
        fx2 = x2 * f2_rh

        dyn_sys = DynSystem([x1, x2], [], [],
                            {x1 : fx1, x2 : fx2},
                            {}, False)
        r0 = Real(0)
        init = _pow(x1,2) - 1 + _pow(x2,2) < Real(Fraction(1,4))
        safe = _pow(x1,2) + _pow(x2,2) < 8

        polynomials = [x1,
                       _pow(x1,2)-3,
                       4*_pow(x1,2)-3,
                       x2,
                       _pow(x1,2) + _pow(x2,2) - 8,
                       _pow(x1,2) + 21*_pow(x2,2)-12,
                       f2_rh]

        return (dyn_sys, TRUE(), polynomials, init, safe, FALSE())


    @unittest.skip("")
    def test_invar_lazy(self):
        test_cases = [TestDecomposition.get_test_case_1(),
                      TestDecomposition.get_test_case_2(),
                      TestDecomposition.get_test_case_3()]

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            invars = get_invar_lazy_set(dyn_sys, invar, poly, init, safe)
            self.assertTrue(self._eq_sets(invars,expected))

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            invars = get_invar_lazy(dyn_sys, invar, poly, init, safe)
            self.assertTrue(self._eq_wformula(invars,expected))

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            invars = dwcl(dyn_sys, invar, poly, init, safe)
            self.assertTrue(self._eq_wformula(invars,expected))

    @unittest.skip("")
    def test_invar_dwcl(self):
        test_cases = [TestDecomposition.get_test_case_4()]

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            invars = dwcl(dyn_sys, invar, poly, init, safe)

            same = _get_solver().is_valid(Iff(invars, expected))

            if not same:
                logger = logging.getLogger(__name__)
                logger.info("%s\nis not:\n%s" % (invars.serialize(),
                                                 expected.serialize))

            self.assertTrue(same)

    @unittest.skip("")
    def test_invar_dwcl_pegasus(self):
        def rf(a,b):
            return Real(Fraction(a,b))

        x, y = [Symbol(var, REAL) for var in ["x", "y"]]

        fx = (rf(-3,2) * x * x +
              rf(-1,2) * x * x * x - y)
        fy = 3 * x - y

        dyn_sys = DynSystem([x, y], [], [],
                            {x : fx, y : fy},
                            {}, False)

        invar = TRUE()
        init = (x*x + rf(1,10) * x  + rf(1,400) +
                y*y + rf(3,100) * y + rf(9,40000)) <= rf(1,5000)

        safe = (rf(49,100)) + x + x * x + y + y * y > 0

        poly = [(
            (rf(366,3125) * (x*x*x*x)) +
            (rf(-5089,200000) * (x*x*x*y)) +
            (rf(-19539,250000) * (x*x*x)) +
            (rf(6907,50000) * (x*x*y*y)) +
            (rf(7757,10000) * (x*x*y)) +
            (rf(13077,10000) * (x*x)) +
            (rf(1,500000) * (x*y*y*y)) +
            (rf(-11411,100000) * (x*y*y)) +
            (rf(-2053,5000) * (x*y)) +
            (rf(1,500000) * (x)) +
            (rf(11777,500000) * (y*y*y*y)) +
            (rf(9201,50000) * (y*y*y)) +
            (rf(25341,50000) * (y*y)) +
            (rf(1,1000000) * (y)) +
            rf(-99997,1000000))]

        invars = dwc(dyn_sys, invar, poly, init, safe)
