""" Test the decomposition encoding
"""

import logging
import unittest
import os
import sys
import tempfile
from fractions import Fraction
from nose.plugins.attrib import attr

try:
    import unittest2 as unittest
except ImportError:
    import unittest



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
from pysmt.exceptions import SolverAPINotFound

from barrier.test import TestCase, skipIfMSaticIsNotAvailable
from barrier.system import DynSystem
from barrier.utils import get_range_from_int, get_mathsat_smtlib
from barrier.lzz.serialization import importInvar

from barrier.formula_utils import FormulaHelper

from barrier.ts import TS
from barrier.msatic3 import MSatic3

from barrier.decomposition.encoding import (
    DecompositionEncoder, DecompositionOptions,
    _get_neigh_encoding
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


    def _prove_ts(self, ts, prop):
        res = None

        try:
            (_, tmp_file) = tempfile.mkstemp(suffix=None,
                                             prefix=None,
                                             dir=None,
                                             text=True)
            with open(tmp_file,"w") as outstream:
                ts.to_vmt(outstream, prop)

            print("Verifying %s..." % tmp_file)
            ic3 = MSatic3()
            res = ic3.solve(tmp_file)
        finally:
            if os.path.isfile(tmp_file):
                os.remove(tmp_file)
        return res

    @attr('msatic3')
    @skipIfMSaticIsNotAvailable()
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
        (ts, p, predicates) = encoder.get_ts_ia()

        res = self._prove_ts(ts, p)
        self.assertTrue(res == MSatic3.Result.SAFE)

    def test_invar_in_init(self):
        env = get_env()

        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "invar_inputs")
        problem_file = os.path.join(input_path, "Constraint-based_Example_7__Human_Blood_Glucose_Metabolism_.invar")
        with open(problem_file, "r") as json_stream:
            problem_list = importInvar(json_stream, env)

        (problem_name, init, safe, dyn_sys, invariants, predicates) = problem_list[0]

        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invariants,
                                        predicates,
                                        init,
                                        safe)
        (ts, p, predicates) = encoder.get_ts_ia()

        all_and_next = set(ts.state_vars)
        all_and_next.update([ts.next_f(v) for v in ts.state_vars])

        self.assertTrue(len(ts.init.get_free_variables().difference(all_and_next)) == 0)
        self.assertTrue(len(p.get_free_variables().difference(all_and_next)) == 0)

    @attr('msatic3')
    @skipIfMSaticIsNotAvailable()
    def test_wiggins(self):
        input_path = self.get_from_path("invar_inputs")
        test_case = os.path.join(input_path, "Wiggins_Example_18_7_3_n.invar")

        print("Reading input...")
        env = get_env()
        with open(test_case, "r") as f:
            problem_list = importInvar(f, env)
            assert(len(problem_list) == 1)

        (problem_name, ant, cons, dyn_sys, invar, predicates) = problem_list[0]

        print(dyn_sys)
        print(ant.serialize())
        print(cons.serialize())
        print(predicates)

        #x = Symbol("_x", REAL)
        #y = Symbol("_y", REAL)
        # p1 = x + 1
        # p2 = y + 1
        # p3 = (
        #     (Real(Fraction(-1,3)) - x) * (Real(Fraction(-1,3)) - x) +
        #     (Real(Fraction(-1,3)) - y) * (Real(Fraction(-1,3)) - y) +
        #     Real(Fraction(-1,16))
        # )
        #p4 = x
        #p5 = y
        #predicates = [p4,p5]

        print("Creating decomposition...")
        # Use rewriting of init and prop
        options = DecompositionOptions(True, True, False)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invar,
                                        predicates,
                                        ant,
                                        cons,
                                        options)
        (ts, p, predicates) = encoder.get_ts_ia()

        print("Printing vmt...")
        with open("/tmp/wiggings.vmt", "w") as outstream:
            ts.to_vmt(outstream, p)

        print("Proving ts...")
        res = self._prove_ts(ts, p)
        self.assertTrue(res == MSatic3.Result.SAFE)

