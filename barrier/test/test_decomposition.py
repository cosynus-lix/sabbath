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
    _get_neighbors,
    get_invar_lazy
)


class TestDecomposition(TestCase):

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

    def get_test_case_1(self):
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


    def get_test_case_2(self):
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

    def get_test_case_3(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(And(Equals(x,r0),y<r0))
        return (dyn_sys, TRUE(),[x,y], init, safe,[])

    def test_invar_lazy(self):
        def eq_sets(got, expected):
            new_exp = set()
            for s in expected:
                new_exp.add(frozenset(s))
            same = got == new_exp

            if not same:
                logger = logging.getLogger(__name__)
                logger.info("RESULT:")

                for abs_state in got:
                    abs_state_str = "p(x) := "
                    for pred in abs_state:
                        abs_state_str += " %s" % pred.serialize()
                    logging.info(abs_state_str)

            return same

        test_cases = [self.get_test_case_1(),
                      self.get_test_case_2(),
                      self.get_test_case_3()]

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t
            invars = get_invar_lazy(dyn_sys, invar, poly, init, safe)
            self.assertTrue(eq_sets(invars,expected))

