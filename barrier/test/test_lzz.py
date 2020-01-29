""" Test the system """


import logging
import unittest
import os
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from multiprocessing import Pool
from multiprocessing.context import TimeoutError

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    is_valid,
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals,
    GE, GT, LT, LE
)
from pysmt.logics import QF_NRA

from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.lzz.lzz import (
    is_p_invar, lzz, get_inf_dnf, get_ivinf_dnf
)

from barrier.lzz.serialization import importLzz
from barrier.lzz.dnf import DNFConverter


def run_lzz(lzz_problem, env):
    with Solver(logic=QF_NRA, name="z3") as solver:
        (name, candidate, dyn_sys, candidate, invar) = lzz_problem
        print("LZZ %s..." % name)
        is_invar = lzz(solver, candidate, dyn_sys, candidate, invar)
    return is_invar


class TestLzz(TestCase):

    def test_lzz_pred(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]
        # der(x) = -2y, der(y) = x^2
        dyn_sys = DynSystem([x, y], [], [],
                        {x : -Fraction(2,1) * y, y : x * x},
                        {})

        init = And(Fraction(0,1) <= x,
                   x <= Fraction(1,2),
                   Fraction(-1,2) <= y,
                   y <= Fraction(3, 5))

        h = GE(-x - y * y, Real(0))
        p = GE(-x * y + y * y, Real(0))

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = is_p_invar(solver, p, dyn_sys, init, h)

        self.assertTrue(is_invar)


    def _get_sys(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]
        # der(x) = -2y, der(y) = x^2
        dyn_sys = DynSystem([x, y], [], [],
                        {x : -Fraction(2,1) * y, y : x * x},
                        {})

        return x, y, dyn_sys


    def test_inf_pred(self):
        x,y,dyn_sys = self._get_sys()

        r0 = Real(0)
        r05 = Fraction(1,2)
        rm05 = Fraction(-1,2)
        preds = [x >= -1, y > rm05]

        expected = [Or(Or(x + 1 > r0,
                          And(Equals(x + 1, r0), -2*y > r0)),
                        And(Equals(x + 1, r0),
                            Equals(-2*y, r0))),
                    Or(y + r05 > r0,
                       And(Equals(y + r05, r0),
                           x * x > r0))]

        for pred, res in zip(preds, expected):
            inf = get_inf_dnf(dyn_sys, pred)
            self.assertTrue(is_valid(Iff(res, inf)))

    def test_ivinf_pred(self):
        x,y,dyn_sys = self._get_sys()

        r0 = Real(0)
        r05 = Fraction(1,2)
        rm05 = Fraction(-1,2)
        preds = [x >= -1, y > rm05]

        expected = [Or(Or(x + 1 > r0,
                          And(Equals(x + 1, r0), 2*y > r0)),
                        And(Equals(x + 1, r0),
                            Equals(-2*y, r0))),
                    Or(y + r05 > r0,
                       And(Equals(y + r05, r0),
                           -1 * (x * x) > r0))]

        for pred, res in zip(preds, expected):
            inf = get_ivinf_dnf(dyn_sys, pred)
            self.assertTrue(is_valid(Iff(res, inf)))

    def test_lzz(self):
        x, y = [Symbol(var, REAL) for var in ["x","y"]]
        # der(x) = -2y, der(y) = x^2
        dyn_sys = DynSystem([x, y], [], [],
                        {x : -Fraction(2,1) * y, y : x * x},
                        {})
        init = GE(x + y, Real(0))

        # x >= -1 or y > -1/2
        candidate = Or(GE(x, Real(Fraction(-1,1))),
                       GT(y, Real(Fraction(-1,2))))

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = lzz(solver, candidate, dyn_sys, init, TRUE())

        self.assertTrue(is_invar)

    def test_lzz_2(self):
        s, v, a, vseg = [Symbol(var, REAL) for var in ["s", "v", "a", "v_seg"]]
        # der(s) = v, der(v) = a
        dyn_sys = DynSystem([s, v], [], [], {s : v, v : a}, {}, False)

        init = v < vseg
        inv = v < vseg
        candidate = inv

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = lzz(solver, candidate, dyn_sys, init, TRUE())

        self.assertTrue(is_invar)

    def test_dnf(self):
        def _test_dnf(forig):
            c = DNFConverter()
            f1 = c.get_dnf(forig)
            self.assertTrue(is_valid(Iff(forig, f1)))

        x, y = [Symbol(var, REAL) for var in ["x","y"]]

        p1 = x + y > 0
        p2 = x > 0
        p3 = y >= 0

        _test_dnf(And(Or(p1,p2), Or(p1,p3), Or(p2)))


    def test_battery(self):
        import barrier.test

        def run_with_timeout(lzz_problem,time_out,env):
            is_invar = None
            try:
                name = lzz_problem[0]
                print("Running %s" % name)
                kwargs = {"lzz_problem": lzz_problem,
                          "env" : env}
                pool = Pool(1)
                future_res_run_lzz = pool.apply_async(run_lzz, kwds=kwargs)
                pool.close()

                # Get result after 10 seconds or kill
                try:
                    # is_invar = run_lzz(lzz_problem, env)
                    is_invar = future_res_run_lzz.get(time_out)
                    is_invar = future_res_run_lzz.get(0)
                    print("%s is %s!" % (name, "True" if is_invar else "False"))
                except TimeoutError:
                    print("%s time out!" % name)
                    is_invar = None
            finally:
                pass

            return is_invar


        current_path = os.path.dirname(os.path.abspath(barrier.test.__file__))
        input_path = os.path.join(current_path, "lzz_inputs")

        env = get_env()

        # Ignore longer checks
        to_ignore = ["3D Lotka Volterra (III)",
            "3D Lotka Volterra (I)",
            "Ben Sassi Girard 20104 Moore-Greitzer Jet",
            "Coupled Spring-Mass System (I)",
            "Coupled Spring-Mass System (II)",
            "3D Lotka Volterra (II)",
            "Longitudinal Motion of an Aircraft",
            "Collision Avoidance Maneuver (I)"]

        for lzz_file in os.listdir(input_path):
            if not lzz_file.endswith(".lzz"):
                continue
            with open(os.path.join(input_path, lzz_file), "r") as f:
                lzz_problem = importLzz(f, env)
                if (not lzz_problem[0] in to_ignore):
                    is_invar = run_lzz(lzz_problem, env)
                    self.assertTrue(is_invar)
