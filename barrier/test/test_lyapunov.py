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
from barrier.test import TestCase, skipIfSOSIsNotAvailable, skipIfPicosIsNotAvailable

from barrier.system import DynSystem
from barrier.lyapunov.lyapunov import (
    synth_lyapunov,
    validate_lyapunov,
    synth_lyapunov_linear
)


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
                       }, {}), False), # not stable, e.g., circle...

            (DynSystem([x1,x2], [], [],
                       {
                         x1 : x1 + Real(3) * x2,
                         x2 : Real(2) * x1
                       }, {}), False), # Unstable, so no lyapunov
        ]
        return systems

    def test_lyapunov_smt(self):
        systems = TestLyapunov.get_test_cases()

        # smt synthesis
        for (sys, expected) in systems:
            (res, lyapunov) = synth_lyapunov(sys, 2, False, True, 20)
            self.assertTrue(res == None or res == expected)
            if (res):
                # correct by construction
                # print(res)
                # print("LYAP ", sys.get_derivator().simplify(lyapunov).serialize())
                # print("LIE  ", sys.get_derivator().get_lie_der(lyapunov).serialize())
                self.assertTrue(validate_lyapunov(sys, lyapunov))

    @attr('sos')
    @skipIfPicosIsNotAvailable()
    @skipIfSOSIsNotAvailable()
    def test_lyapunov_sos(self):
        # Test SOS formulation
        systems = TestLyapunov.get_test_cases()
        for (sys, expected) in systems:
            (res, lyapunov) = synth_lyapunov(sys, 2, False, False)
            # print(res, expected)
            # expected -> res (all the others cannot be checked)
            self.assertTrue((not expected) or res)
            if (res and expected):
                is_valid = validate_lyapunov(sys, lyapunov)
                if (not is_valid):
                    print("Lyapunov function is not valid: ", lyapunov.serialize())
                self.assertTrue(is_valid)


    @attr('sos')
    @skipIfPicosIsNotAvailable()
    @skipIfSOSIsNotAvailable()
    def test_common_lyapunov(self):
        # Test SOS formulation
        systems = TestLyapunov.get_test_cases()
        for (sys, expected) in systems:
            (res, lyapunov) = synth_lyapunov(sys, 2, False, False)
            # expected -> res (all the others cannot be checked)
            self.assertTrue((not expected) or res)
            if (res and expected):
                is_valid = validate_lyapunov(sys, lyapunov)
                if (not is_valid):
                    print("Lyapunov function is not valid: ", lyapunov.serialize())
                self.assertTrue(is_valid)

    def test_lyapunov_direct(self):
        systems = TestLyapunov.get_test_cases()

        for use_smt in [True, False]:
            for (sys, expected) in systems:
                (res, lyap) = synth_lyapunov_linear(sys, use_smt)

                self.assertTrue(res == expected)

                # Should be correct by construction
                if (expected):
                    self.assertTrue(validate_lyapunov(sys, lyap))
