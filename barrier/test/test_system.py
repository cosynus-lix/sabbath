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
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real, Equals
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne, is_valid
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


    def test_rescale(self):

        var = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        sys = DynSystem(var, [], [],
                        {var[0] :  var[0]*Real(2) + var[1]*Real(3) - Real(4),
                         var[1] :  var[0] + var[1]*Real(2) + Real(1)},
                        {})

        new_systems = sys.get_rescaled_by_equilibrium_point()
        self.assertTrue(len(new_systems) == 1)
        new_sys = new_systems[0][0]
        sol = new_systems[0][1]

        rename = {new_sys._states[0] : sys._states[0],
                  new_sys._states[1] : sys._states[1]}

        other_ode = new_sys.get_ode(new_sys._states[0])
        self.assertTrue(is_valid(Equals(other_ode.substitute(rename),
                                 sys.get_ode(var[0]) + Real(4))))

        other_ode = new_sys.get_ode(new_sys._states[1])
        self.assertTrue(is_valid(Equals(other_ode.substitute(rename),
                                 sys.get_ode(var[1]) - Real(1))))

        self.assertTrue(is_valid(Equals(sys.get_ode(var[0]).substitute(sol),
                                        Real(0))))

        self.assertTrue(is_valid(Equals(sys.get_ode(var[1]).substitute(sol),
                                        Real(0))))

