""" Test the system """


import logging
import unittest
import os
from functools import partial
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

from multiprocessing import Pool
from multiprocessing.context import TimeoutError

from pysmt.exceptions import SolverAPINotFound
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

import barrier.test
from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.lzz.lzz import (
    is_p_invar, lzz, get_inf_dnf, get_ivinf_dnf
)

from barrier.lie import Derivator
from barrier.lzz.serialization import importLzz, importInvar
from barrier.lzz.dnf import DNFConverter


from barrier.mathematica.mathematica import get_mathematica
from barrier.utils import get_mathsat_smtlib


def run_lzz(lzz_problem, env, solver = None):
    if solver is None:
        solver = Solver(logic=QF_NRA, name="z3")

    (name, candidate, dyn_sys, invar) = lzz_problem
    is_invar = lzz(solver, candidate, dyn_sys.get_derivator(), candidate, invar)

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

        expected = [
            Or([r0 < x + 1,
                And([Equals(x + 1, r0), Equals(-2*y, r0),r0 < -2*x*x]),
                And([Equals(x + 1, r0), -2*y > r0]),
                And([Equals(x + 1, r0), Equals(-2*y, r0), Equals(-2*x*x, r0)])
            ]),
            Or([
                And([Equals(x * y * -4, r0),
                     Equals(y + r05, r0),
                     r0 < -4*x*x*x + + 8*y*y,
                     Equals(r0, x * x)]),
                0.0 < (y + r05),
                And([r0 < x * y * -4,
                     Equals(y + r05, r0),
                     Equals(x * x, r0)]),
                And([Equals(y + r05, r0),
                     r0 < x * x])
            ])
        ]

        derivator = dyn_sys.get_derivator()
        for pred, res in zip(preds, expected):
            inf = get_inf_dnf(derivator, pred)
            self.assertTrue(is_valid(Iff(res, inf)))

    def test_ivinf_pred(self):
        x,y,dyn_sys = self._get_sys()

        r0 = Real(0)
        r05 = Fraction(1,2)
        rm05 = Fraction(-1,2)
        preds = [x >= -1, y > rm05]

        expected = [
            Or([And([0.0 < (x * x * -2), Equals(x + 1, r0), Equals(y * -2,r0)]),
                r0 < x + 1,
                And([r0 < (r0 - (y * -2)), Equals(x + 1 , r0)]),
                And([Equals(x + 1,r0),
                     Equals(-2 * y,r0),
                     Equals(-2 * x * x,r0)])
            ]),
            Or([And([Equals(x * y * - 4,r0),
                     (r0 < (r0 - ((x * x * x * - 4) + (y * y * 8.0)))),
                     Equals((x * x),r0),
                     Equals(y + r05,r0)
                ]),
                And([r0 < (r0 - (x * x)),
                     Equals((y + r05),r0)
                ]),
                And([r0 < (x * y * - 4),
                     Equals(x * x,r0),
                     Equals(y + r05,r0)
                ]),
                r0 < y + r05
            ])
        ]

        derivator = dyn_sys.get_derivator()
        for pred, res in zip(preds, expected):
            inf = get_ivinf_dnf(derivator, pred)

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
        is_invar = lzz(solver, candidate, dyn_sys.get_derivator(), init, TRUE())

        self.assertTrue(is_invar)

    def test_lzz_2(self):
        s, v, a, vseg = [Symbol(var, REAL) for var in ["s", "v", "a", "v_seg"]]
        # der(s) = v, der(v) = a
        dyn_sys = DynSystem([s, v, a, vseg], [], [],
                            {s : v,
                             v : a,
                             a : Real(0),
                             vseg : Real(0)}, {}, False)
        init = v < vseg
        inv = v < vseg
        candidate = inv

        solver = Solver(logic=QF_NRA, name="z3")
        is_invar = lzz(solver, candidate, dyn_sys.get_derivator(), init, v < vseg)

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
        long_tests = [
            "3D Lotka Volterra (III)",
            "3D Lotka Volterra (I)",
            "Coupled Spring-Mass System (II)",
            "3D Lotka Volterra (II)",
            "Longitudinal Motion of an Aircraft",
            "Van der Pol Fourth Quadrant",
            "Dumortier Llibre Artes Ex. 10_15_ii",
            "Constraint-based Example 8 (Phytoplankton Growth)",
            "Collision Avoidance Maneuver (I)",
            "Bhatia Szego Ex_2_4 page 68" # because of rank computation
        ]


        long_tests_smt = ["Dumortier Llibre Artes Ex. 1_9b",
                          "Dumortier Llibre Artes Ex. 10_15_i",
                          "Ben Sassi Girard 20104 Moore-Greitzer Jet",
                          "Strogatz Example 6_3_2"]

        long_tests_z3 = [] + long_tests_smt

        long_tests_msat = [] + long_tests_smt + ["Coupled Spring-Mass System (I)",
                                                 "Ben Sassi Girard Sankaranarayanan 2014 Fitzhugh-Nagumo"]

        long_tests_mathematica = ["Strogatz Exercise 7_3_5"]

        # Ignore checks with ghost variables in the invariant
        # We do not support that.
        not_supported = [
            # has ghost variables
            "Looping Particle",
            # has function symbols
            "Nonlinear Circuit Example 1+2 (Tunnel Diode Oscillator)",
            # contains old operator (old(v) refers to the value of v before time elapse)
            "Collision Avoidance Maneuver (II)",
            "Collision Avoidance Maneuver (III)"]

        all_solvers = [("msathsat-smtlib",partial(get_mathsat_smtlib,
                                                  env=get_env())),
                       ("z3", partial(Solver,
                                      logic=QF_NRA,
                                      name="z3")),
                       ("mathematica", partial(get_mathematica,
                                               env=get_env(),
                                               budget_time=0))]

        solvers = []
        for (name, f) in all_solvers:
            try:
                solver_instance = f()
                solver_instance.is_sat(TRUE())
                solvers.append((name,f))
            except Exception:
                logging.debug("Skipping not found solver %s..." % name)
                pass

        for (solver_name, solver_init) in solvers:
            print("Running solver %s..." % solver_name)

            for lzz_file in os.listdir(input_path):
                if not lzz_file.endswith(".lzz"):
                    continue
                with open(os.path.join(input_path, lzz_file), "r") as f:
                    lzz_problem = importLzz(f, env)

                    solver = solver_init()
                    assert(not solver is None)

                    if (solver_name == "msathsat-smtlib"):
                        to_ignore = long_tests + not_supported + long_tests_msat
                    elif (solver_name == "z3"):
                        to_ignore = long_tests + not_supported + long_tests_z3
                    elif (solver_name == "mathematica"):
                        to_ignore = long_tests + not_supported + long_tests_mathematica

                    if (not lzz_problem[0] in to_ignore):
                        print("Running LZZ problem from %s (%s)..." % (lzz_file, lzz_problem[0]))
                        is_invar = run_lzz(lzz_problem, env, solver)
                        self.assertTrue(is_invar)

                    solver.exit()
                    solver = None

    def test_import_invar(self):
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "invar_inputs")

        env = get_env()

        for invar_file in os.listdir(input_path):
            with open(os.path.join(input_path, invar_file), "r") as json_stream:
                problem_list = importInvar(json_stream, env)
                assert(len(problem_list) == 1)
                for p in problem_list:
                    (problem_name, ant, cons, dyn_sys, invar, predicates) = p

    def test_import_invar_input(self):
        input_path = self.get_from_path("invar_inputs")
        test_case = os.path.join(input_path, "Constraint-based_Example_7__Human_Blood_Glucose_Metabolism_.invar")

        env = get_env()

        with open(test_case, "r") as f:
            problem_list = importInvar(f, env)
            assert(len(problem_list) == 1)

            (problem_name, ant, cons, dyn_sys, invar, predicates) = problem_list[0]

            u_var = Symbol("_u", REAL)
            found_u = False
            for i in dyn_sys.inputs():
                if i == u_var:
                    found_u = True
            self.assertTrue(found_u)


