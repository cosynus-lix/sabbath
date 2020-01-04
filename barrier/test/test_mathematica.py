""" Test the mathematica solver """

import logging
import unittest
import os
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from pysmt.logics import QF_NRA
from pysmt.environment import Environment
from pysmt.typing import BOOL, REAL, INT, FunctionType, BV8, BVType
from pysmt.shortcuts import (
  Symbol, is_sat, Not, Implies, GT, Plus, Int, Real,
  Minus, Times, Xor, And, Or, TRUE, Iff, FALSE, Ite,
  Equals,LT,GT,LE,GE
)

from barrier.test import TestCase
from barrier.mathematica.mathematica import (
  MathematicaSolver,
  MathematicaConverter,
)

class TestConverter(TestCase):

  def test_allowed(self):
    env = Environment()
    convert = MathematicaConverter(env)

    x,y,z = [Symbol(s,REAL) for s in ["x","y","z"]]
    test_cases = [
      (x,"(x)"),
      #
      (Plus(x,y), "Plus[(x), (y)]"),
      (Minus(x,y), "Plus[(x), Minus[(y)]]"),
      (Times(x,y), "Times[(x), (y)]"),
      #
      (Equals(x,y), "Equal[(x), (y)]"),
      (LT(x,y), "Less[(x), (y)]"),
      (LE(x,y), "LessEqual[(x), (y)]"),
      #
      (And(LT(x,y),LT(x,z)), "And[Less[(x), (y)], Less[(x), (z)]]"),
      (Or(LT(x,y),LT(x,z)), "Or[Less[(x), (y)], Less[(x), (z)]]"),
      (Not(LT(x,y)), "Not[Less[(x), (y)]]"),
      (Iff(LT(x,y),LT(x,z)), "Equivalent[Less[(x), (y)], Less[(x), (z)]]"),
      (Implies(LT(x,y),LT(x,z)), "Implies[Less[(x), (y)], Less[(x), (z)]]"),
      (Ite(LT(x,y),LT(x,z),LT(x,y)),
       "And[Implies[Less[(x), (y)], Less[(x), (z)]], Implies[Not[Less[(x), (y)]], Less[(x), (y)]]]"),
#      (And(x,y), "And[(x), (y)]")
    ]


    for (pysmt_expr, math_expr) in test_cases:
      res = convert.convert(pysmt_expr)
      res_str = str(res)
      # print(math_expr)
      # print(res_str)
      self.assertTrue(res_str == math_expr)

class TestMathematica(TestCase):
  def test_solve(self):
    env = Environment()
    solver = MathematicaSolver(env, QF_NRA)


    x,y,z = [Symbol(s,REAL) for s in ["x","y","z"]]

    formula = And(x*x + y*y >= 3, x > 0)
    solver.add_assertion(formula)

    self.assertTrue(solver.solve())

    solver.reset_assertions()
    solver.add_assertion(formula)
    solver.add_assertion(x < 0)
    self.assertFalse(solver.solve())

    solver.reset_assertions()
    solver.add_assertion(formula)
    solver.push()
    solver.add_assertion(x < 0)
    self.assertFalse(solver.solve())
    solver.pop()
    self.assertTrue(solver.solve())
