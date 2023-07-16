""" Test the decomposition encoding
"""

import logging
import unittest
import os
import sys
from io import StringIO
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

from barrier.test import TestCase, skipIfMSaticIsNotAvailable, skipIfIc3IAIsNotAvailable
from barrier.system import DynSystem
from barrier.utils import get_range_from_int, get_mathsat_smtlib

from barrier.serialization.invar_serialization import importInvarVer
from barrier.serialization.hybrid_serialization import importHSVer, serializeHS

from barrier.decomposition.predicates import AbsPredsTypes, get_predicates, get_polynomials_ha
from barrier.lzz.lzz import LzzOpt

from barrier.formula_utils import FormulaHelper

from barrier.ts import TS
from barrier.vmt.vmt_engines import MSatic3, Ic3IA, VmtResult, prove_ts

from barrier.decomposition.encoding import (
    DecompositionEncoder, DecompositionOptions,
    _get_neigh_encoding,
    DecompositionEncoderHA
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
                                        safe,
                                        DecompositionOptions(),
                                        None,
                                        True)
        (ts, p) = encoder.get_quantified_ts()
        (ts, p, predicates) = encoder.get_ts_ia()

        res = prove_ts(ts, p)
        self.assertTrue(res == VmtResult.SAFE)

    def test_invar_in_init(self):
        env = get_env()

        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "invar_inputs")
        problem_file = os.path.join(input_path, "Constraint-based_Example_7__Human_Blood_Glucose_Metabolism_.invar")
        with open(problem_file, "r") as json_stream:
            problem_list = importInvarVer(json_stream, env)

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
            problem_list = importInvarVer(f, env)
            assert(len(problem_list) == 1)

        (problem_name, ant, cons, dyn_sys, invar, predicates) = problem_list[0]

        # print(dyn_sys)
        # print(ant.serialize())
        # print(cons.serialize())
        # print(predicates)

        x = Symbol("_x", REAL)
        y = Symbol("_y", REAL)
        p1 = x + 1
        p2 = y + 1
        p4 = x
        p5 = y

        options = DecompositionOptions(False, False, False, False)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invar,
                                        [p5],
                                        ant,
                                        cons,
                                        options)
        (ts, p, predicates) = encoder.get_ts_ia()
        self.assertTrue(prove_ts(ts, p) == VmtResult.UNSAFE)


        options = DecompositionOptions(False, False, False, False)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invar,
                                        [p1,p2,p4,p5],
                                        ant,
                                        cons,
                                        options)
        (ts, p, predicates) = encoder.get_ts_ia()
        self.assertTrue(prove_ts(ts, p) == VmtResult.SAFE)


    @attr('msatic3')
    @skipIfMSaticIsNotAvailable()
    def test_hs(self):
        input_path = self.get_from_path("hybrid_inputs")
        env = get_env()

        models = [
            ("disc1.hyb", VmtResult.SAFE),
            ("disc2.hyb", VmtResult.UNSAFE),
            ("disc3.hyb", VmtResult.UNSAFE),
            ("disc4.hyb", VmtResult.SAFE),
            ("disc5.hyb", VmtResult.SAFE),
            ("disc6.hyb", VmtResult.SAFE),
            ("disc7.hyb", VmtResult.UNSAFE),
            ("disc8.hyb", VmtResult.SAFE),
            ("cont1.hyb", VmtResult.UNSAFE),
            ("cont2.hyb", VmtResult.SAFE),
            ("hyb_fc.hyb", VmtResult.SAFE)
        ]

        for (m,expected) in models:
            with open(os.path.join(input_path, m), "r") as f:
                problem = importHSVer(f, env)
                ha = problem.ha
                prop = problem.prop
                predicates = problem.predicates

                options = DecompositionOptions(False, False, False, False)
                encoder = DecompositionEncoderHA(env, ha, predicates, prop,
                                                 options, None)
                (ts, p, predicates) = encoder.get_ts_ia()


                # print("Final trans")
                # print(ts.trans.serialize())
                # # Debug
                outstream = StringIO()
                with open("/tmp/app.smt2", "w") as f:
                    ts.to_vmt(f, p)
                # print(outstream.getvalue())
                # print(ts.trans.serialize())

                print(ts.trans.serialize())

                self.assertTrue(prove_ts(ts, p) == expected)


    def test_hs_hscc(self):
        input_path = self.get_from_path("hybrid_inputs")
        env = get_env()

        with open(os.path.join(input_path, "hybrid_controller_hscc17.hyb"), "r") as f:
            problem = importHSVer(f, env)
            ha = problem.ha
            prop = problem.prop
            predicates = problem.predicates

            abs_type = (AbsPredsTypes.FACTORS.value)
            polynomials = get_polynomials_ha(ha, prop, abs_type, env)

            lzz_opt = LzzOpt(True, True)
            options = DecompositionOptions(False, False, False, False, lzz_opt)
            encoder = DecompositionEncoderHA(env, ha, polynomials, prop,
                                             options, None)
            (ts, p, predicates) = encoder.get_ts_ia()

            with open("/tmp/hscc2017.smt2", "w") as f:
                ts.to_vmt(f, p)

            with open("/tmp/hscc2017.preds", "w") as outstream:
                ts.dump_predicates(outstream, predicates)

            # self.assertTrue(prove_ts(ts, p) == VmtResult.SAFE)
