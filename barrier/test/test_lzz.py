""" Test the system """


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
from barrier.test import TestCase, skipIfMathematicaIsNotAvailable

from barrier.system import DynSystem
from barrier.lzz.lzz import (
    is_p_invar, lzz, get_inf_dnf, get_ivinf_dnf,
    get_generic_set,
    get_inf_op_remainders,
    LzzOpt
)

from barrier.lie import Derivator
from barrier.lzz.serialization import importLzz, importInvar
from barrier.lzz.dnf import DNFConverter


from barrier.mathematica.mathematica import get_mathematica, MathematicaSession
from barrier.utils import get_mathsat_smtlib
from barrier.formula_utils import has_vars_in_divisor


def run_lzz(opt, lzz_problem, env, solver = None):
    if solver is None:
        solver = Solver(logic=QF_NRA, name="z3")

    (name, candidate, dyn_sys, invar) = lzz_problem

    is_invar = lzz(opt, solver, candidate, dyn_sys.get_derivator(), candidate, invar)

    return is_invar

def get_lzz_opts():
    opts = [LzzOpt(),LzzOpt(False, False), LzzOpt(True,False), LzzOpt(True,True)]
    return opts

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

    # TO REMOVE: we support the direct encoding of equalities 
    # def test_unsupported(self):
    #     x,y,dyn_sys = self._get_sys()
    #     derivator = dyn_sys.get_derivator()
    #     lzz_opt = LzzOpt()

    #     pred = Equals(x,Real(0))

    #     with self.assertRaises(Exception):
    #         get_inf_dnf(lzz_opt, derivator, None, pred)
    #     with self.assertRaises(Exception):
    #         get_ivinf_dnf(lzz_opt, derivator, None, pred)

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
            for opt in get_lzz_opts():
                inf = get_inf_dnf(opt, derivator, None, pred)
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
        for opt in get_lzz_opts():
            print(opt)
            for pred, res in zip(preds, expected):
                inf = get_ivinf_dnf(opt, derivator, None, pred)
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

        for opt in get_lzz_opts():
            is_invar = lzz(opt, solver, candidate, dyn_sys.get_derivator(), init, TRUE())
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
        for opt in get_lzz_opts():
            is_invar = lzz(opt, solver, candidate, dyn_sys.get_derivator(), init, v < vseg)
            self.assertTrue(is_invar)

    # TO FIX
    # def test_dnf(self):
    #     def _test_dnf(forig):
    #         c = DNFConverter()
    #         f1 = c.get_dnf(forig)
    #         self.assertTrue(is_valid(Iff(forig, f1)))

    #     x, y = [Symbol(var, REAL) for var in ["x","y"]]

    #     p1 = x + y > 0
    #     p2 = x > 0
    #     p3 = y >= 0

    #     _test_dnf(And(Or(p1,p2), Or(p1,p3), Or(p2)))

    def get_lzz_problems(self, input_path, solver_name):
        # Ignore longer checks
        long_tests = [
            "3D_Lotka_Volterra__III_.lzz",
            "3D_Lotka_Volterra__II_.lzz",
            "3D_Lotka_Volterra__I_.lzz",
            "Coupled_Spring-Mass_System__II_.lzz",
            "Longitudinal_Motion_of_an_Aircraft.lzz",
            "Van_der_Pol_Fourth_Quadrant.lzz",
            "Dumortier_Llibre_Artes_Ex._10_15_ii.lzz",
            "Constraint-based_Example_8_Phytoplankton_Growth_.lzz",
            "Collision_Avoidance_Maneuver__I_.lzz",
            "Bhatia_Szego_Ex_2_4_page_68.lzz" # because of rank computation
        ]

        long_tests_smt = ["Dumortier_Llibre_Artes_Ex._1_9b.lzz",
                          "Dumortier_Llibre_Artes_Ex._10_15_i.lzz",
                          "Ben_Sassi_Girard_20104_Moore-Greitzer_Jet.lzz",
                          "Ben_Sassi_Girard_Sankaranarayanan_2014_Fitzhugh-Nagumo.lzz",
                          "Strogatz_Example_6_3_2.lzz"]

        long_tests_z3 = [] + long_tests_smt
        long_tests_msat = [] + long_tests_smt + [
            "Stable_Limit_Cycle_2.lzz",
            "Ben_Sassi_Girard_Sankaranarayanan_2014_Fitzhugh-Nagumo.lzz",
            "Strogatz_Exercise_7_3_5.lzz",
            "MIT_astronautics_Lyapunov.lzz",
            "Unstable_Unit_Circle_2.lzz",
            "Unstable_Unit_Circle_1.lzz",
            "Arrowsmith_Place_Fig_3_1_page_72.lzz",
            "Man_Maccallum_Goriely_Page_57.lzz"]

        long_tests_mathematica = ["Strogatz_Exercise_7_3_5.lzz",
                                  "Nonlinear_Circuit_Example_3.lzz",
                                  "Nonlinear_Circuit_Example_4.lzz",
                                  "Constraint-based_Example_8__Phytoplankton_Growth_.lzz",
                                  "Liu_Zhan_Zhao_Emsoft11_Example_25.lzz",
                                  "Hybrid_Controller_Mode_2.lzz",
                                  "Hybrid_Controller_Mode_1.lzz"]

        # Ignore checks with ghost variables in the invariant
        # We do not support that.
        not_supported = [
            # has ghost variables
            "Looping_Particle.lzz",
            # has function symbols
            "Nonlinear_Circuit_Example_1_2__Tunnel_Diode_Oscillator_.lzz",
            # contains old operator (old(v) refers to the value of v before time elapse)
            "Collision_Avoidance_Maneuver__II_.lzz",
            "Collision_Avoidance_Maneuver__III_.lzz"]


        if (solver_name == "msathsat-smtlib"):
            to_ignore = long_tests + not_supported + long_tests_msat
        elif (solver_name == "z3"):
            to_ignore = long_tests + not_supported + long_tests_z3
        elif (solver_name == "mathematica"):
            to_ignore = long_tests + not_supported + long_tests_mathematica

        lzz_problems = []
        for lzz_file in os.listdir(input_path):
            if not lzz_file.endswith(".lzz"):
                continue
            if not (os.path.basename(lzz_file) in to_ignore):
                lzz_problems.append(lzz_file)

        return lzz_problems

    def _run_lzz_solver(self, solver_name, solver_init):
        input_path = self.get_from_path("lzz_inputs")
        env = get_env()

        try:
            solver_instance = solver_init()
            solver_instance.is_sat(TRUE())

            print("Running solver %s..." % solver_name)

            lzz_files = self.get_lzz_problems(input_path, solver_name)
            for lzz_file in lzz_files:
                with open(os.path.join(input_path, lzz_file), "r") as f:
                    lzz_problem = importLzz(f, env)

                for opt in get_lzz_opts():
                    solver = solver_init()
                    assert(not solver is None)

                    print("Running LZZ problem from %s (%s)..." % (lzz_file, lzz_problem[0]))
                    is_invar = run_lzz(opt, lzz_problem, env, solver)
                    self.assertTrue(is_invar)

                    solver.exit()
                    solver = None
        finally:
            MathematicaSession.terminate_session()


    @attr('long')
    def test_battery_z3(self):
        self._run_lzz_solver("z3", partial(Solver, logic=QF_NRA, name="z3"))

    @attr('long')
    def test_battery_mathsat(self):
        self._run_lzz_solver("msathsat-smtlib", partial(get_mathsat_smtlib,env=get_env()))

    @attr('long')
    @attr('mathematica')
    @skipIfMathematicaIsNotAvailable()
    def test_battery_mathematica(self):
        self._run_lzz_solver("mathematica", partial(get_mathematica, env=get_env(),budget_time=0))


    def test_models_with_div(self):
        env = get_env()
        input_path = self.get_from_path("lzz_inputs")

        for lzz_file in os.listdir(input_path):
            if (not lzz_file.endswith("*.lzz")):
                continue

            with open(os.path.join(input_path, lzz_file), "r") as json_stream:
                p= importLzz(json_stream, env)

                (name, candidate, dyn_sys, invar) = p

                div_candidate = has_vars_in_divisor(candidate)
                div_invar = has_vars_in_divisor(invar)
                div_ode = reduce(lambda acc , y : (acc or has_vars_in_divisor(y)),
                                 [rhs for lhs,rhs in dyn_sys.get_odes().items()],
                                 False)

                if (div_candidate or div_invar or div_ode):
                    print("%s contains division by non-constants (" \
                          "candidate: %d, invar: %d, ode: %d)" % (name,
                                                                  div_candidate,
                                                                  div_invar,
                                                                  div_ode))
                self.assertFalse(div_candidate or div_invar or div_ode)
