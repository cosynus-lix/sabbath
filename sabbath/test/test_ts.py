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

from nose.plugins.attrib import attr

from pysmt.typing import BOOL
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne
from pysmt.shortcuts import is_valid, is_sat, reset_env
from pysmt.typing import REAL
from pysmt.exceptions import SolverAPINotFound

from sabbath.test import TestCase, skipIfMSaticIsNotAvailable, skipIfIc3IAIsNotAvailable
from sabbath.ts import TS, ImplicitAbstractionEncoder
from sabbath.vmt.vmt_engines import MSatic3, Ic3IA

class TestSystem(TestCase):

    def setUp(self):
        print("SETUP")
        self.env = reset_env()

    def test_ts(self):
        def test_ts_impl(ts, safe, env):
            outstream = StringIO()
            ts.to_vmt(outstream, safe)
            outstream.seek(0)
            (ts_new, safe_new) = TS.from_vmt(outstream, env)
            self.assertTrue(is_valid(Iff(ts.init, ts_new.init)))
            self.assertTrue(is_valid(Iff(ts.trans, ts_new.trans)))
            self.assertTrue(is_valid(Iff(safe, safe_new)))

        def test_ts_file(filename):
            with open(filename, "r") as f:
                (ts, safe) = TS.from_vmt(f)
                test_ts_impl(ts, safe, self.env)

        self.env = get_env()

        x,y,z = Symbol("x"), Symbol("y"), Symbol("z")
        next_x,next_y,next_z = Symbol("x_next"), Symbol("y_next"), Symbol("z_next")

        next_f = lambda l : {x : next_x, y : next_y, z : next_z }[l]

        ts = TS(self.env,
                [x,y,z], next_f,
                And(x,y),
                And(And(Iff(next_x, x), Implies(x, next_y)),
                    Iff(z, Not(next_x))))
        test_ts_impl(ts, TRUE(), self.env)

        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "vmt_models")
        for f in os.listdir(input_path):
            if f.endswith("smt2") or f.endswith("vmt"):
                test_ts_file(os.path.join(input_path, f))



    def test_serialize_to_mcmt(self):
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "vmt2mcmt_models")

        #for f in os.listdir(input_path):
        #    if f.endswith("smt2") or f.endswith("vmt"):

        vmt_model_filename = os.path.join(input_path, "etcs.vmt")
        with open(vmt_model_filename, "r") as f:
            (ts, safe) = TS.from_vmt(f)

            outstream = StringIO()
            ts.to_mcmt(outstream, safe)
            outstream.seek(0)

            print(outstream.getvalue())


    def _aux_test_impl_abs(self, get_vmt_engine):
        long_tests = set(["toy",
                          "mem_slave_tlm.1",
                          "pipeline",
                          "kundu-bug-1"])

        env = get_env()
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "vmt_models")
        pred_files = os.listdir(input_path)
        for predfile in pred_files:
            print("Processing %s" % predfile)
            if not predfile.endswith("preds"):
                continue

            base = os.path.splitext(os.path.basename(predfile))[0]
            smtfile = os.path.join(input_path, "%s.smt2" % base)
            if not os.path.isfile(smtfile):
                continue
            if (base in long_tests):
                print("Skipping long test %s" % smtfile)
                continue

            with open(smtfile, "r") as f:
                print("Reading %s" % smtfile)
                (ts, safe) = TS.from_vmt(f, env)

            with open(os.path.join(input_path, predfile), "r") as f:
                predicates = ts.read_predicates(f)

            ic3 = get_vmt_engine()
            print("Verifying using IA...")
            res_orig = ic3.solve(smtfile)

            print("\n---\nChecking encodings\n---\n")

            enc_1 = ImplicitAbstractionEncoder(ts, safe, predicates, env, True, True, False)
            enc_2 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, True)
            enc_3 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, False)

            enc_4 = ImplicitAbstractionEncoder(ts, safe, predicates, env, True, True, False, True)
            enc_5 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, True, True)
            enc_6 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, False, True)

            for enc in [enc_1, enc_2, enc_3]:
            # for enc in [enc_4, enc_5, enc_6]:
                ts_abs = enc.get_ts_abstract()
                safe_abs = enc.get_prop_abstract()

                outfile = os.path.join(input_path, "%s_abs.smt2" % base)
                with open(outfile, "w") as f:
                    ts_abs.to_vmt(f, safe_abs)
                    f.close()

                print("Verifying %s..." % base)

                ic3 = get_vmt_engine()
                print("Verifying using fixed IA encoding...")
                res = ic3.solve(outfile)
                self.assertTrue(res == res_orig)

                os.remove(outfile)
            print("Verified result %s" % str(res_orig))

    @attr('msatic3')
    @skipIfMSaticIsNotAvailable()
    def test_impl_abs_msatic3(self):
        init_f = lambda : MSatic3()
        self._aux_test_impl_abs(init_f)

    @attr('ic3ia')
    @skipIfIc3IAIsNotAvailable()
    def test_impl_abs_ic3ia(self):
        init_f = lambda : Ic3IA()
        self._aux_test_impl_abs(init_f)

