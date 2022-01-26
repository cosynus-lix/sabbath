""" Test the lyapunov function computation """


import logging
import unittest
import os
from functools import partial, reduce
from fractions import Fraction


try:
    import unittest2 as unittest
except ImportError:
    import unittest

from nose.plugins.attrib import attr

from pysmt.shortcuts import Real

import barrier.test
from barrier.test import TestCase, skipIfSOSIsNotAvailable

from barrier.system import DynSystem
from barrier.lyapunov import synth_lyapunov, validate_lyapunov


from pysmt.shortcuts import Symbol, REAL


class TestLyapunov(TestCase):

    @staticmethod
    def get_test_cases():
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        systems = [
            (DynSystem([x1,x2], [], [],
                       {
                         x1 : -2 * x1,
                         x2 : x1 - x2
                       }, {}), True),

            (DynSystem([x1,x2], [], [],
                       {
                         x1 : x2,
                         x2 : -x1
                       }, {}), True),

            (DynSystem([x1,x2], [], [],
                       {
                         x1 : x1 + Real(3) * x2,
                         x2 : Real(2) * x1
                       }, {}), None), # Unstable, so no lyapunov
        ]
        return systems

    def test_lyapunov_smt(self):
        systems = TestLyapunov.get_test_cases()

        # smt synthesis
        for (sys, expected) in systems:
            (res, lyapunov) = synth_lyapunov(sys, 2, False, True)
            self.assertTrue(res == expected)
            if (expected):
                # correct by construction
                self.assertTrue(validate_lyapunov(sys, lyapunov))

    @attr('sos')
    @skipIfSOSIsNotAvailable()
    def test_lyapunov_sos(self):
        # Test SOS formulation
        systems = TestLyapunov.get_test_cases()
        for (sys, expected) in systems:
            print("a")
            (res, lyapunov) = synth_lyapunov(sys, 2, False, False)
            print(res, expected)
            # expected -> res (all the others cannot be checked)
            self.assertTrue((not expected) or res)
            if (res and expected):
                is_valid = validate_lyapunov(sys, lyapunov)
                if (not is_valid):
                    print("Lyapunov function is not valid: ", lyapunov.serialize())
                self.assertTrue(is_valid)

