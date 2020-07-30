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
from pysmt.shortcuts import is_valid
from pysmt.typing import REAL
from pysmt.exceptions import SolverAPINotFound

from barrier.test import TestCase, skipIfMSaticIsNotAvailable
from barrier.ts import TS, ImplicitAbstractionEncoder
from barrier.msatic3 import MSatic3

class TestSystem(TestCase):

    def test_ts(self):
        def test_ts_impl(ts, safe):
            outstream = StringIO()
            ts.to_vmt(outstream, safe)
            outstream.seek(0)
            (ts_new, safe_new) = TS.from_vmt(outstream)
            self.assertTrue(is_valid(Iff(ts.init, ts_new.init)))
            self.assertTrue(is_valid(Iff(ts.trans, ts_new.trans)))
            self.assertTrue(is_valid(Iff(safe, safe_new)))

        def test_ts_file(filename):
            with open(filename, "r") as f:
                (ts, safe) = TS.from_vmt(f)
                test_ts_impl(ts, safe)

        env = get_env()

        x,y,z = Symbol("x"), Symbol("y"), Symbol("z")
        next_x,next_y,next_z = Symbol("x_next"), Symbol("y_next"), Symbol("z_next")

        next_f = lambda l : {x : next_x, y : next_y, z : next_z }[l]

        ts = TS(env,
                [x,y,z], next_f,
                And(x,y),
                And(And(Iff(next_x, x), Implies(x, next_y)),
                    Iff(z, Not(next_x))))
        test_ts_impl(ts, TRUE())


        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "vmt_models")
        for f in os.listdir(input_path):
            if f.endswith("smt2") or f.endswith("vmt"):
                test_ts_file(os.path.join(input_path, f))


    @attr('msatic3')
    @skipIfMSaticIsNotAvailable()
    def test_impl_abs(self):
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


            try:
                ic3 = MSatic3()

                print("Verifying using IA...")
                res_orig = ic3.solve(smtfile)
            except SolverAPINotFound:
                print("MSatic3 not found...")
                logging.debug("MSatic3 not found...")
                continue

            enc_1 = ImplicitAbstractionEncoder(ts, safe, predicates, env, True, True, False)
            enc_2 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, True)
            enc_3 = ImplicitAbstractionEncoder(ts, safe, predicates, env, False, False, False)

            for enc in [enc_1, enc_2, enc_3]:
                ts_abs = enc.get_ts_abstract()
                safe_abs = enc.get_prop_abstract()

                outfile = os.path.join(input_path, "%s_abs.smt2" % base)
                with open(outfile, "w") as f:
                    ts_abs.to_vmt(f, safe_abs)
                    f.close()

                print("Verifying %s..." % base)
                try:
                    ic3 = MSatic3()

                    print("Verifying using fixed IA encoding...")
                    res = ic3.solve(outfile)

                    self.assertTrue(res == res_orig)
                except SolverAPINotFound:
                    print("MSatic3 not found...")
                    logging.debug("MSatic3 not found...")
                os.remove(outfile)
            print("Verified result %s" % str(res_orig))


