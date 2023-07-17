""" Test the transition system """

import logging
import unittest
import os
import sys
from io import StringIO

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from pysmt.typing import BOOL
from pysmt.shortcuts import (
    get_env,
    Not, And, Or, Implies, Iff,
    Symbol,
    TRUE, FALSE,
    GE, LE, LT, GT, Equals,
    Plus,
    Real,
    is_valid
)

from pysmt.typing import REAL, BOOL
from pysmt.exceptions import SolverAPINotFound

from sabbath.test import TestCase
from sabbath.formula_utils import PredicateExtractor

class TestFormula(TestCase):
    def test_predicates(self):
        env = get_env()
        x,y,z = [Symbol(c, REAL) for c in ["x","y","z"]]
        p1 = Equals(Plus(x,y), Real(0))

        extr = PredicateExtractor(env)

        expected = set([p1])
        extr.add_predicates_from(p1)
        self.assertTrue(expected == extr.get_predicates())

        p2 = Symbol("a", BOOL)
        expected.add(p2)
        extr.add_predicates_from(p2)
        self.assertTrue(expected == extr.get_predicates())

        p3 = x + 5 >= 0
        p4 = x <= 0
        p5 = z - x <= z * z
        expected.add(p3)
        expected.add(p4)
        expected.add(p5)
        extr.add_predicates_from(And(p3, Or(p4, p5)))
        self.assertTrue(expected == extr.get_predicates())

        extr.add_predicates_from(And(p3, Or(p4, p5)))
        self.assertTrue(expected == extr.get_predicates())


