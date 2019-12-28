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
from barrier.utils import get_range

from barrier.decomposition.explicit import (
    get_invar_lazy
)


class TestDecomposition(TestCase):

    def get_test_case(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        return dyn_sys

    def test_invar_lazy(self):
        dyn_sys = self.get_test_case()

        [x,y] = [s for s in dyn_sys.states()]

        init = get_range([x, y],
                         [(Real(Fraction(-1,1)),
                           Real(Fraction(-2,1))),
                          (Real(Fraction(-1,1)),
                           Real(Fraction(-2,1)))])

        target = get_range([x, y],
                           [(Real(Fraction(1,1)),
                             Real(Fraction(2,1))),
                            (Real(Fraction(1,1)),
                             Real(Fraction(2,1)))])
        safe = Not(target)

        invars = get_invar_lazy(dyn_sys, TRUE(), [y, x],
                                init, safe)
