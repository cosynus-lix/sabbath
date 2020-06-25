""" Test the system """


import logging
import unittest
import os

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from pysmt.typing import BOOL
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne
from pysmt.typing import REAL

from barrier.test import TestCase
from barrier.system import DynSystem, MalformedSystem


class TestSystem(TestCase):

    def test_create(self):
        def check_sys(states, inputs, disturbances, odes, dist):
            """
            Check that we store the data in the system
            """
            dyn = DynSystem(states, inputs, disturbances, odes, dist)
            for (x1, x2) in zip(dyn.states(), states):
                self.assertTrue(x1 is x2)
            for (x1, x2) in zip(dyn.inputs(), inputs):
                self.assertTrue(x1 is x2)
            for (x1, x2) in zip(dyn.disturbances(), disturbances):
                self.assertTrue(x1 is x2)
            for (x1, x2) in zip(dyn.odes(), odes): self.assertTrue(x1 is x2)
            for (x1, x2) in zip(dyn.dist_constraints(), dist):
                self.assertTrue(x1 is x2)


        st = [Symbol("x%s" % (i+1), REAL) for i in range(10)]
        inp = [Symbol("u%s" % (i+1), REAL) for i in range(10)]
        dist = [Symbol("n%s" % (i+1), REAL) for i in range(10)]

        check_sys(st[:2], [], [],
                  {st[0] :  -st[1], st[1] :  -st[0]},
                  {})

        check_sys(st[:2], inp[:3], dist[:1],
                  {st[0] :  -st[1], st[1] :  -st[0] + inp[0] + dist[0]},
                  {dist[0] : GE(dist[0], Real(0))})


        # ode with no vars
        with self.assertRaises(MalformedSystem):
            DynSystem([], [], [], {}, {})

        # ode with var not declared
        with self.assertRaises(MalformedSystem):
            DynSystem(st[:1], [], [], {st[0] :  -st[1]}, {})

        # ode with var not declared
        with self.assertRaises(MalformedSystem):
            DynSystem(st[:1], [], [], {st[0] :  -inp[1]}, {})

        # Not enough odes
        with self.assertRaises(MalformedSystem):
            DynSystem(st[:2], [], [], {st[0] :  -st[1]}, {})

        # Not enough dist constraints
        with self.assertRaises(MalformedSystem):
            DynSystem(st[:2], inp[:2], dist[:2],
                      {st[0] :  -st[1], st[1] :  -st[0]},
                      {})



