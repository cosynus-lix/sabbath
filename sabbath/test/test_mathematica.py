""" Test the mathematica solver """

import logging
import unittest
import os
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from nose.plugins.attrib import attr

from pysmt.logics import QF_NRA
from pysmt.environment import Environment
from pysmt.typing import BOOL, REAL, INT, FunctionType, BV8, BVType
from pysmt.shortcuts import (
    Symbol, is_sat, Not, Implies, GT, Plus, Int, Real,
    Minus, Times, Xor, And, Or, TRUE, Iff, FALSE, Ite, Div,
    Equals,LT,GT,LE,GE,
    get_env, Solver
)
from pysmt.exceptions import SolverAPINotFound
from pysmt.smtlib.parser import SmtLibParser

from sabbath.test import TestCase, skipIfMathematicaIsNotAvailable
from sabbath.mathematica.mathematica import (
    MathematicaSolver,
    MathematicaConverter,
    get_mathematica,
    MathematicaSession
)

class TestConverter(TestCase):

  @attr('mathematica')
  @skipIfMathematicaIsNotAvailable()
  def test_allowed(self):
      env = Environment()
      convert = MathematicaConverter(env)

      x,y,z = [Symbol(s,REAL) for s in ["x","y","z"]]
      test_cases = [
          (x,"Global`x"),
          #
          (Plus(x,y), "Plus[Global`x, Global`y]"),
          (Minus(x,y), "Plus[Global`x, Minus[Global`y]]"),
          (Times(x,y), "Times[Global`x, Global`y]"),
          (Div(x,y), "Divide[Global`x, Global`y]"),
          #
          (Equals(x,y), "Equal[Global`x, Global`y]"),
          (LT(x,y), "Less[Global`x, Global`y]"),
          (LE(x,y), "LessEqual[Global`x, Global`y]"),
          #
          (And(LT(x,y),LT(x,z)), "And[Less[Global`x, Global`y], Less[Global`x, Global`z]]"),
          (Or(LT(x,y),LT(x,z)), "Or[Less[Global`x, Global`y], Less[Global`x, Global`z]]"),
          (Not(LT(x,y)), "Not[Less[Global`x, Global`y]]"),
          (Iff(LT(x,y),LT(x,z)), "Equivalent[Less[Global`x, Global`y], Less[Global`x, Global`z]]"),
          (Implies(LT(x,y),LT(x,z)), "Implies[Less[Global`x, Global`y], Less[Global`x, Global`z]]"),
          (Ite(LT(x,y),LT(x,z),LT(x,y)),
         "And[Implies[Less[Global`x, Global`y], Less[Global`x, Global`z]], Implies[Not[Less[Global`x, Global`y]], Less[Global`x, Global`y]]]"),
      ]


      for (pysmt_expr, math_expr) in test_cases:
          res = convert.convert(pysmt_expr)
          res_str = str(res)
          self.assertTrue(res_str == math_expr)

class TestMathematica(TestCase):

    @attr('mathematica')
    @skipIfMathematicaIsNotAvailable()
    def test_solve(self):
        env = Environment()

        try:
            solver = get_mathematica(env)

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
        except SolverAPINotFound:
            print("Mathematica not found - skipping test...")
        finally:
            MathematicaSession.terminate_session()


class TestFindMin(TestCase):
    @attr('mathematica')
    @skipIfMathematicaIsNotAvailable()
    def test_solve(self):
        def test_approx(solver, val, expected):
            if (expected is None) != (val is None):
                return False
            elif (expected is None and val is None):
                return True
            else:
                delta = Real(Fraction(1,1000))
                in_range = And(
                    [
                        LE(val, expected + delta),
                        GE(val, Minus(expected, delta)),
                    ]
                )
                return solver.is_sat(in_range)

        env = get_env()
        try:
            solver = get_mathematica(env)

            x,y = [Symbol(s,REAL) for s in ["x","y"]]

            test_cases = [
                (x,LE(x*x + y*y - 1, Real(0)),Real(-1)),
                (x, GE(x,Real(0)), Real(0)),
                (x, LE(x,Real(0)), None), # No minimum
            ]

            for (f, const, expected) in test_cases:
                (min_value, min_model) = solver.find_min(f, const)
                self.assertTrue(test_approx(solver, min_value, expected))

            test_cases = [
                (x,LE(x*x + y*y - 1, Real(0)), Real(1)),
                (x, GE(x,Real(0)), None), # No maximum
                (x, LE(x,Real(0)), Real(0)),
            ]

            for (f, const, expected) in test_cases:
                (max_value, max_model) = solver.find_max(f, const)
                self.assertTrue(test_approx(solver, max_value, expected))

        except SolverAPINotFound:
            print("Mathematica not found - skipping test...")
        finally:
            MathematicaSession.terminate_session()
