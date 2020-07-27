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

from barrier.test import TestCase, skipIfMathematicaIsNotAvailable
from barrier.mathematica.mathematica import (
    MathematicaSolver,
    MathematicaConverter,
    get_mathematica
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
          (Div(x,y), "Divide[(x), (y)]"),
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

    @attr('mathematica')
    @skipIfMathematicaIsNotAvailable()
    def test_bug_sat(self):
        env = Environment()
        solver = get_mathematica(env)
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "test_smt")
        input_file = os.path.join(input_path, "bug_z3.smt2")
        with open(input_file, "r") as instream:
            parser = SmtLibParser(env)
            script = parser.get_script(instream)
            formula = script.get_last_formula()
            self.assertTrue(solver.is_sat(formula))


    @attr('mathematica')
    @skipIfMathematicaIsNotAvailable()
    def test_bug_sat_pysmt(self):
        env = get_env()

        l = ["_m1","_m2","_k1","_k2","_v1","_v2","_x1","_x2","_u1","_u8","_u10"]
        _m1,_m2,_k1,_k2,_v1,_v2,_x1,_x2,_u1,_u8,_u10 = [Symbol(v, REAL) for v in l]

        # parse the smt2 file
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "test_smt")
        input_file = os.path.join(input_path, "bug_z3.smt2")
        with open(input_file, "r") as instream:
            parser = SmtLibParser(env)
            script = parser.get_script(instream)
        orig_formula = script.get_last_formula()

        m2inv = Real(1) / _m2;
        m1inv = Real(1) / _m1;
        k2m1u8 = _k2 * _m1 * _u8;
        k1m2u8 = _k1 * _m2 * _u8;

        lhs = Equals(((((((((_u8 * _v1) * _v2) + ((((_k2 * _x1) * _x2) * ((_m1 * _u8) - ((Real(2) * _m2) * _u10))) / (_m1 * _m2))) + (_u10 * (_v1 * (_v1)))) + _u1) + (((Real(Fraction(1,2)) * (_v2 * (_v2))) * (((k1m2u8 - k2m1u8) + ((_k2 * _m2) * _u8)) + (((Real(2) * _k2) * _m2) * _u10))) / (_k2 * _m1))) + (((Real(Fraction(1,2)) * (((((Real(2) * _k1) * _m2) * _u10) - k2m1u8) + (((Real(2) * _k2) * _m2) * _u10))) * (_x1 * (_x1))) / (_m1 * _m2))) + (((Real(Fraction(1,2)) * ((k1m2u8 - k2m1u8) + (((Real(2) * _k2) * _m2) * _u10))) * (_x2 * (_x2))) / (_m1 * _m2))), Real(0))

        rhs_and_1 = Or(
                    (Real(0) < (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))))
                    ,
                    And(
                        (Real(0) < ((_v1 * ((_x1 * m1inv * m2inv * ((Real(-1) * k2m1u8) + (Real(2) * _k1 * _m2 * _u10) + (Real(2) * _m2 * _u10 * _k2))) + (_x2 * _k2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (_v2 * ((_x2 * m1inv * m2inv * (k1m2u8 + (Real(-1) * k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) + (_x1 * _k2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (((Real(-1) * _x1 * _k1 * m1inv) + (Real(-1) * _k2 * m1inv * (_x1 + (Real(-1) * _x2)))) * ((_v2 * _u8) + (Real(2) * _u10 * _v1))) + (Real(-1) * _k2 * m2inv * (_x2 + (Real(-1) * _x1)) * ((_u8 * _v1) + (_v2 * m1inv * (Real(1) / _k2) * (k1m2u8 + (_m2 * _k2 * _u8) + (Real(-1) * k2m1u8) + (Real(2) * _m2 * _u10 * _k2)))))))
                        ,
                        Equals((((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))), Real(0))
                    )
                    ,
                    And(
                        Equals((((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))), Real(0)),
                        Equals(((_v1 * ((_x1 * m1inv * m2inv * ((Real(-1) * k2m1u8) + (Real(2) * _k1 * _m2 * _u10) + (Real(2) * _k2 * _m2 * _u10))) + (_k2 * _x2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (_v2 * ((_x2 * m1inv * m2inv * (k1m2u8 + (Real(-1) * k2m1u8) + (Real(2) * _k2 * _m2 * _u10))) + (_k2 * _x1 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (((_u8 * _v2) + (Real(2) * _u10 * _v1)) * ((Real(-1) * _k1 * _x1 * m1inv) + (Real(-1) * _k2 * m1inv * (_x1 + (Real(-1) * _x2))))) + (Real(-1) * _k2 * m2inv * (_x2 + (Real(-1) * _x1)) * ((_u8 * _v1) + (_v2 * (Real(1) / _k2) * m1inv * (k1m2u8 + (_k2 * _m2 * _u8) + (Real(-1) * k2m1u8) + (Real(2) * _k2 * _m2 * _u10)))))), Real(0))
                    )
                )

        rhs_and_2 = (
            Or(
                (Real(0) < (Real(0) - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))))),
                (
                    And(
                        (Real(0) < ((_v1 * ((Real(-1) * _x1 * m1inv * m2inv * ((Real(-1) * k2m1u8) + (Real(2) * _k1 * _m2 * _u10) + (Real(2) * _m2 * _u10 * _k2))) + (Real(-1) * _x2 * _k2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (_v2 * ((Real(-1) * _x2 * m1inv * m2inv * (k1m2u8 + (Real(-1) * k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) + (Real(-1) * _x1 * _k2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (((Real(-1) * _x1 * _k1 * m1inv) + (Real(-1) * _k2 * m1inv * (_x1 + (Real(-1) * _x2)))) * ((Real(-1) * _v2 * _u8) + (-Real(2) * _u10 * _v1))) + (Real(-1) * _k2 * m2inv * (_x2 + (Real(-1) * _x1)) * ((Real(-1) * _u8 * _v1) + (Real(-1) * _v2 * m1inv * (Real(1) / _k2) * (k1m2u8 + (_m2 * _k2 * _u8) + (Real(-1) * k2m1u8) + (Real(2) * _m2 * _u10 * _k2))))))),
                        Equals((Real(0) - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1)))), Real(0))
                    )
                ),
                (
                    And(
                        Equals((Real(0) - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (Real(2) * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((Fraction(1,2) * _v2 * _v2 * (((k1m2u8 - k2m1u8) + (_m2 * _k2 * _u8)) + (Real(2) * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((Fraction(1,2) * _x1 * _x1 * (((Real(2) * _k1 * _m2 * _u10) - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((Fraction(1,2) * _x2 * _x2 * ((k1m2u8 - k2m1u8) + (Real(2) * _m2 * _u10 * _k2))) / (_m2 * _m1)))), Real(0)),
                        Equals(((_v1 * ((Real(-1) * _x1 * m1inv * m2inv * ((Real(-1) * k2m1u8) + (Real(2) * _k1 * _m2 * _u10) + (Real(2) * _k2 * _m2 * _u10))) + (Real(-1) * _k2 * _x2 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (_v2 * ((Real(-1) * _x2 * m1inv * m2inv * (k1m2u8 + (Real(-1) * k2m1u8) + (Real(2) * _k2 * _m2 * _u10))) + (Real(-1) * _k2 * _x1 * m1inv * m2inv * ((_m1 * _u8) + (-Real(2) * _m2 * _u10))))) + (((Real(-1) * _u8 * _v2) + (-Real(2) * _u10 * _v1)) * ((Real(-1) * _k1 * _x1 * m1inv) + (Real(-1) * _k2 * m1inv * (_x1 + (Real(-1) * _x2))))) + (Real(-1) * _k2 * m2inv * (_x2 + (Real(-1) * _x1)) * ((Real(-1) * _u8 * _v1) + (Real(-1) * _v2 * (Real(1) / _k2) * m1inv * (k1m2u8 + (_k2 * _m2 * _u8) + (Real(-1) * k2m1u8) + (Real(2) * _k2 * _m2 * _u10)))))), Real(0))
                    )
                )
            )
        )


        # z3 = Solver(logic=QF_NRA, name="z3")
        # print("Checking if valid")
        # self.assertTrue(z3.is_valid(Iff(rhs, orig_formula)))
        # print("checked...")


        # what="""((((0.0 < (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1)))) | ((0.0 < ((_v1 * ((_x1 * (1.0 / _m1) * (1.0 / _m2) * ((-1.0 * _k2 * _m1 * _u8) + (2.0 * _k1 * _m2 * _u10) + (2.0 * _m2 * _u10 * _k2))) + (_x2 * _k2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (_v2 * ((_x2 * (1.0 / _m1) * (1.0 / _m2) * ((_k1 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _m2 * _u10 * _k2))) + (_x1 * _k2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (((-1.0 * _x1 * _k1 * (1.0 / _m1)) + (-1.0 * _k2 * (1.0 / _m1) * (_x1 + (-1.0 * _x2)))) * ((_v2 * _u8) + (2.0 * _u10 * _v1))) + (-1.0 * _k2 * (1.0 / _m2) * (_x2 + (-1.0 * _x1)) * ((_u8 * _v1) + (_v2 * (1.0 / _m1) * (1.0 / _k2) * ((_k1 * _m2 * _u8) + (_m2 * _k2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _m2 * _u10 * _k2))))))) & ((((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) = 0.0))) | (((((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) = 0.0) & (((_v1 * ((_x1 * (1.0 / _m1) * (1.0 / _m2) * ((-1.0 * _k2 * _m1 * _u8) + (2.0 * _k1 * _m2 * _u10) + (2.0 * _k2 * _m2 * _u10))) + (_k2 * _x2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (_v2 * ((_x2 * (1.0 / _m1) * (1.0 / _m2) * ((_k1 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _k2 * _m2 * _u10))) + (_k2 * _x1 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (((_u8 * _v2) + (2.0 * _u10 * _v1)) * ((-1.0 * _k1 * _x1 * (1.0 / _m1)) + (-1.0 * _k2 * (1.0 / _m1) * (_x1 + (-1.0 * _x2))))) + (-1.0 * _k2 * (1.0 / _m2) * (_x2 + (-1.0 * _x1)) * ((_u8 * _v1) + (_v2 * (1.0 / _k2) * (1.0 / _m1) * ((_k1 * _m2 * _u8) + (_k2 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _k2 * _m2 * _u10)))))) = 0.0))) & (((0.0 < (0.0 - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))))) | ((0.0 < ((_v1 * ((-1.0 * _x1 * (1.0 / _m1) * (1.0 / _m2) * ((-1.0 * _k2 * _m1 * _u8) + (2.0 * _k1 * _m2 * _u10) + (2.0 * _m2 * _u10 * _k2))) + (-1.0 * _x2 * _k2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (_v2 * ((-1.0 * _x2 * (1.0 / _m1) * (1.0 / _m2) * ((_k1 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _m2 * _u10 * _k2))) + (-1.0 * _x1 * _k2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (((-1.0 * _x1 * _k1 * (1.0 / _m1)) + (-1.0 * _k2 * (1.0 / _m1) * (_x1 + (-1.0 * _x2)))) * ((-1.0 * _v2 * _u8) + (-2.0 * _u10 * _v1))) + (-1.0 * _k2 * (1.0 / _m2) * (_x2 + (-1.0 * _x1)) * ((-1.0 * _u8 * _v1) + (-1.0 * _v2 * (1.0 / _m1) * (1.0 / _k2) * ((_k1 * _m2 * _u8) + (_m2 * _k2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _m2 * _u10 * _k2))))))) & ((0.0 - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1)))) = 0.0))) | (((0.0 - (((((((_v2 * _u8 * _v1) + ((_x1 * _x2 * _k2 * ((_m1 * _u8) - (2.0 * _m2 * _u10))) / (_m2 * _m1))) + (_u10 * _v1 * _v1)) + _u1) + ((1/2 * _v2 * _v2 * ((((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (_m2 * _k2 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_k2 * _m1))) + ((1/2 * _x1 * _x1 * (((2.0 * _k1 * _m2 * _u10) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1))) + ((1/2 * _x2 * _x2 * (((_k1 * _m2 * _u8) - (_k2 * _m1 * _u8)) + (2.0 * _m2 * _u10 * _k2))) / (_m2 * _m1)))) = 0.0) & (((_v1 * ((-1.0 * _x1 * (1.0 / _m1) * (1.0 / _m2) * ((-1.0 * _k2 * _m1 * _u8) + (2.0 * _k1 * _m2 * _u10) + (2.0 * _k2 * _m2 * _u10))) + (-1.0 * _k2 * _x2 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (_v2 * ((-1.0 * _x2 * (1.0 / _m1) * (1.0 / _m2) * ((_k1 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _k2 * _m2 * _u10))) + (-1.0 * _k2 * _x1 * (1.0 / _m1) * (1.0 / _m2) * ((_m1 * _u8) + (-2.0 * _m2 * _u10))))) + (((-1.0 * _u8 * _v2) + (-2.0 * _u10 * _v1)) * ((-1.0 * _k1 * _x1 * (1.0 / _m1)) + (-1.0 * _k2 * (1.0 / _m1) * (_x1 + (-1.0 * _x2))))) + (-1.0 * _k2 * (1.0 / _m2) * (_x2 + (-1.0 * _x1)) * ((-1.0 * _u8 * _v1) + (-1.0 * _v2 * (1.0 / _k2) * (1.0 / _m1) * ((_k1 * _m2 * _u8) + (_k2 * _m2 * _u8) + (-1.0 * _k2 * _m1 * _u8) + (2.0 * _k2 * _m2 * _u10)))))) = 0.0))))"""
        # self.assertTrue(what == orig_formula.serialize())

        print(rhs_and_1.serialize())
        print(orig_formula.serialize())

        solver = get_mathematica(env)
        self.assertTrue(solver.is_valid(Iff(And(rhs_and_1, rhs_and_2), orig_formula)))


