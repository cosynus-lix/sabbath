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

    def get_test_case(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        return dyn_sys

    def test_get_neighbors(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]

        r0 = Real(0)
        poly = [x, y]

        tc = [
            # (x<0,y<0) -> [(x=0,y=0),(x<0,y=0),(x=0,y<0)]
            ({LT(x, r0), LT(y, r0)},
             [{Equals(x, r0), Equals(y, r0)},
              {LT(x, r0), Equals(y, r0)},
              {Equals(x, r0), LT(y, r0)}]),
            # (x=0,y=0) -> [(x<0,y<0),(x<0,y=0),(x<0,y>0),
            #               (x>0,y<0),(x>0,y=0),(x>0,y>0),
            #               (x=0,y<0),(x=0,y>0)]
            ({Equals(x, r0), Equals(y, r0)},
             [{LT(x,r0),LT(y,r0)},
              {LT(x,r0),Equals(y,r0)},
              {LT(x,r0),LT(r0,y)},
              {LT(r0,x),LT(y,r0)},
              {LT(r0,x),Equals(y,r0)},
              {LT(r0,x),LT(r0,y)},
              {Equals(x,r0), LT(y,r0)},
              {Equals(x,r0),LT(r0,y)},
             ]),
            # (x=0,y<0) -> [(x=0,y=0),(x<0,y<0),(x>0,y<0)]
            ({Equals(x, r0), LT(y, r0)},
             [{Equals(x, r0), Equals(y, r0)},
              {LT(x, r0), LT(y, r0)},
              {LT(r0, x), LT(y, r0)}]),
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

    def test_invar_lazy(self):
        dyn_sys = self.get_test_case()

        [x,y] = [s for s in dyn_sys.states()]
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        target = get_range_from_int([x, y], [(1,2),(1,2)])
        safe = Not(target)

        invars = get_invar_lazy(dyn_sys, TRUE(), [y, x],
                                init, safe)

        expected_invar = set([frozenset({LT(x,r0),LT(y,r0)}),
                              frozenset({LT(x,r0),Equals(y,r0)}),
                              frozenset({LT(x,r0),LT(r0,y)}),
                              frozenset({Equals(x,r0),LT(y,r0)}),
                              frozenset({LT(r0,x),LT(y,r0)})])

        # print("RESULT:")
        # for abs_state in invars:
        #     sys.stdout.write("p(x) := ")
        #     for pred in abs_state:
        #         sys.stdout.write(" %s" % pred.serialize())
        #     print("")

        self.assertTrue(expected_invar == invars)

