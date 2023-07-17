import logging
import unittest
import os

try:
    import unittest2 as unittest
except ImportError:
    import unittest

try:
    from StringIO import StringIO
except ImportError:
    from io import StringIO

import sys

from pysmt.typing import BOOL
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real, Solver, is_valid
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne, Equals
from pysmt.typing import REAL
from pysmt.logics import QF_NRA

from sabbath.test import TestCase
from sabbath.system import DynSystem, HybridAutomaton, MalformedSystem

from sabbath.serialization.hybrid_serialization import importHSVer, serializeHS

from sabbath.test.test_system import TestHS

class TestSerialization(TestCase):
    def testRead(self):
        def _eq_prop_loc(problem1, problem2):
            if len(problem1.prop.prop_by_loc) != len(problem2.prop.prop_by_loc):
                return False
            for (loc, val1) in problem1.prop.prop_by_loc.items():
                val2 = problem2.prop.prop_by_loc[loc]
                if not is_valid(Iff(val1, val2)):
                    return False
            return True

        input_path = self.get_from_path("hybrid_inputs")
        env = get_env()

        ha_files = []
        for f in os.listdir(input_path):
            if not f.endswith(".hyb"):
                continue
            ha_files.append(f)

        for fname in ha_files:
            with open(os.path.join(input_path, fname), "r") as f:
                problem = importHSVer(f, env)

                outstream = StringIO()
                serializeHS(outstream, problem, env)

                outstream.seek(0)
                problem2 = importHSVer(outstream, env)
                self.assertTrue(problem.name == problem2.name and
                                is_valid(Iff(problem.prop.global_prop,problem2.prop.global_prop)) and
                                _eq_prop_loc(problem, problem2) and
                                TestHS.ha_eq(problem.ha, problem2.ha))

