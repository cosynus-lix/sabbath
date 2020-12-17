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

from barrier.test import TestCase
from barrier.system import DynSystem, HybridAutomaton, MalformedSystem

from barrier.serialization.hybrid_serialization import importHSVer, serializeHS

from barrier.test.test_system import TestHS

class TestSerialization(TestCase):
    def testRead(self):
        input_path = self.get_from_path("hybrid_inputs")
        env = get_env()

        ha_files = []
        for f in os.listdir(input_path):
            if not f.endswith(".hyb"):
                continue
            ha_files.append(f)

        for fname in ha_files:
            with open(os.path.join(input_path, fname), "r") as f:
                (name, ha, prop, predicates) = importHSVer(f, env)

                outstream = StringIO()
                serializeHS(outstream, name, ha, prop, predicates, env)
                outstream.seek(0)

                (name2, ha2, prop2, predicates2) = importHSVer(outstream, env)
                self.assertTrue(name == name2 and
                                is_valid(Iff(prop,prop2)),
                                TestHS.ha_eq(ha, ha2))

