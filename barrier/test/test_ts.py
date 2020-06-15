""" Test the transition system """

import logging
import unittest
import os

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from io import StringIO

from pysmt.typing import BOOL
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne
from pysmt.shortcuts import is_valid
from pysmt.typing import REAL

from barrier.test import TestCase
from barrier.ts import TS

class TestSystem(TestCase):
    def test_ts(self):
        def test_ts_impl(ts, safe):
            outstream = StringIO()
            ts.to_vmt(safe, outstream)
            outstream.seek(0)
            (ts_new, safe_new) = TS.from_vmt(outstream)
            self.assertTrue(is_valid(Iff(ts.init, ts_new.init)))
            self.assertTrue(is_valid(Iff(ts.trans, ts_new.trans)))
            self.assertTrue(is_valid(Iff(safe, safe_new)))

        def test_ts_file(filename):
            with open(filename, "r") as f:
                (ts, safe) = TS.from_vmt(f)
                test_ts_impl(ts, safe)


        x,y,z = Symbol("x"), Symbol("y"), Symbol("z")
        next_x,next_y,next_z = Symbol("x_next"), Symbol("y_next"), Symbol("z_next")

        next_f = lambda l : {x : next_x, y : next_y, z : next_z }[l]

        ts = TS([x,y,z], next_f,
                And(x,y),
                And(And(Iff(next_x, x), Implies(x, next_y)),
                    Iff(z, Not(next_x))))
        test_ts_impl(ts, TRUE())


        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "vmt_models")
        for f in os.listdir(input_path):
            test_ts_file(os.path.join(input_path, f))
