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
from pysmt.shortcuts import (
    Symbol, TRUE, FALSE, get_env, GE, Real, Equals, Solver,
    Not, And, Or, Implies, Iff, ExactlyOne, is_valid
)
from pysmt.typing import REAL
from pysmt.logics import QF_NRA

from barrier.test import TestCase
from barrier.system import DynSystem, HybridAutomaton, MalformedSystem
from barrier.ts import TS

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

        eq_0 = {new_sys._states[0] : Real(0),
                new_sys._states[1] : Real(0)}

        other_ode = new_sys.get_ode(new_sys._states[0])
        self.assertTrue(is_valid(Equals(other_ode.substitute(eq_0),
                                        Real(0))))
        self.assertTrue(is_valid(Equals(other_ode.substitute(rename),
                                 sys.get_ode(var[0]) + Real(4))))

        other_ode = new_sys.get_ode(new_sys._states[1])
        self.assertTrue(is_valid(Equals(other_ode.substitute(eq_0),
                                        Real(0))))
        self.assertTrue(is_valid(Equals(other_ode.substitute(rename),
                                 sys.get_ode(var[1]) - Real(1))))

        self.assertTrue(is_valid(Equals(sys.get_ode(var[0]).substitute(sol),
                                        Real(0))))
        self.assertTrue(is_valid(Equals(sys.get_ode(var[1]).substitute(sol),
                                        Real(0))))

class TestHS(TestCase):
    @staticmethod
    def ha_eq(ha1, ha2):
        solver = Solver(logic=QF_NRA, name="z3")

        if ( not (set(ha1._disc_vars) == set(ha2._disc_vars) and
                  set(ha1._cont_vars) == set(ha2._cont_vars))):
            return False

        if (not (len(ha1._init) == len(ha2._init) and
                 len(ha1._locations) == len(ha2._locations) and
                 len(ha1._edges) == len(ha2._edges))):
            return False

        for (src, f1) in ha1._init.items():
            f2 = ha2._init[src]
            if (not solver.is_valid(Iff(f1,f2))):
                return False

        for (src, loc1) in ha1._locations.items():
            loc2 = ha2._locations[src]

            if (not solver.is_valid(Iff(loc1.invar,loc2.invar))):
                return False

        for (src, edge1_list) in ha1._edges.items():
            edge2_list = ha2._edges[src]
            for (edge1, edge2) in zip(edge1_list, edge2_list):
                if (not solver.is_valid(Iff(edge1.trans, edge2.trans))):
                    return False
        return True


    def test_hs(self):
        def get_hs(hs):
            ha2 = HybridAutomaton(hs._disc_vars,hs._cont_vars,
                                  hs._init,
                                  hs._locations,
                                  hs._edges)
            return ha2

        env = get_env()
        x,y,z = [Symbol(l, REAL) for l in ["x","y","z"]]
        a,b,c = [Symbol(l, REAL) for l in ["a","b","c"]]
        f_next = TS.get_next_f([x,y,z], env)
        x_next, y_next, z_next, a_next, b_next, c_next = [f_next(l) for l in [x,y,z,a,b,c]]

        cont_vars = [x]
        disc_vars = [a,b]
        init = {1 : TRUE()}
        locs = {
            1 : HybridAutomaton.Location(invar=TRUE(),
                                         vector_field=DynSystem(cont_vars,
                                                                disc_vars,[],
                                                                {x : x+a},
                                                                {},
                                                                True)),
            2 : HybridAutomaton.Location(invar=TRUE(),
                                         vector_field=DynSystem(states=cont_vars,
                                                                inputs=disc_vars,disturbances=[],
                                                                odes={x:x+a},
                                                                dist_constraints={}))
        }
        edges = {
            1 : [HybridAutomaton.Edge(dst=2, trans=Equals(x_next, x+a)),
                 HybridAutomaton.Edge(dst=1, trans=Equals(x_next, x))]
        }

        ha1 = HybridAutomaton(disc_vars, cont_vars, init, locs, edges)

        self.assertTrue(set(ha1._cont_vars) == set(cont_vars) and
                        set(ha1._disc_vars) == set(disc_vars) and
                        len(ha1._init) == len(init) and
                        len(ha1._locations) == len(locs) and
                        len(ha1._edges) == len(edges))

        ha2 = get_hs(ha1)
        self.assertTrue(TestHS.ha_eq(ha1, ha2))


