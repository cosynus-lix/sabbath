""" Test the decomposition encoding
"""

import logging
import unittest
import os

from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from functools import partial

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
from barrier.lzz.serialization import importInvar

from barrier.lzz.lzz import lzz
from barrier.formula_utils import FormulaHelper

from barrier.decomposition.encoding import (
    DecompositionEncoder, _get_neigh_encoding
)


class TestDecompositionEncoding(TestCase):

    def test_neigh_encoding(self):
        poly = [Symbol(var, REAL) for var in ["x","y"]]

        x = poly[0]
        y = poly[1]
        vars = [x,y]

        next_p = lambda x : partial(FormulaHelper.rename_formula,
                                    env = get_env(),
                                    vars = vars,
                                    suffix = "_next")(formula=x)

        res = _get_neigh_encoding(poly, next_p)

        x_next = FormulaHelper.rename_formula(get_env(),vars, "_next", x)
        y_next = FormulaHelper.rename_formula(get_env(),vars, "_next", y)

        r0 = Real(0)
        expected = Or(
            And(
                And(And(Implies(x > r0, Or(Equals(x_next, r0), x_next > r0)),
                        Implies(x < r0, Or(Equals(x_next, r0), x_next < r0))),
                    Implies(Equals(x,r0), Equals(x_next,r0))),
                And(And(Implies(y > r0, Or(Equals(y_next, r0), y_next > r0)),
                        Implies(y < r0, Or(Equals(y_next, r0), y_next < r0))),
                    Implies(Equals(y,r0), Equals(y_next,r0))),
            ),
            And(
                And(Implies(x > r0, x_next > r0),
                    Implies(x < r0, x_next < r0)),
                And(Implies(y > r0, y_next > r0),
                    Implies(y < r0, y_next < r0))
            )
        )

        self.assertTrue(is_valid(Iff(res, expected)))


    def test_enc(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(get_range_from_int([x, y], [(1,2),(1,2)]))

        encoder  = DecompositionEncoder(get_env(),
                                        dyn_sys,
                                        TRUE(),
                                        [x,y],
                                        init,
                                        safe)
        (ts, p) = encoder.get_quantified_ts()
        (ts, p) = encoder.get_ts()

        # TODO: add test about encoding correctness
        self.assertTrue(True)
