""" Test the system """


import logging
import unittest
import os
from fractions import Fraction
from functools import partial

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import sys

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
from barrier.utils import get_range_from_int

from barrier.lzz.serialization import importInvar

from barrier.lzz.lzz import lzz

from barrier.decomposition.explicit import (
    Result,
    _get_solver,
    _get_neighbors,
    _set_to_formula,
    get_invar_lazy_set,
    get_invar_lazy,
    dwc,
    dwcl
)

from barrier.utils import get_mathsat_smtlib
from barrier.mathematica.mathematica import get_mathematica
from pysmt.exceptions import SolverAPINotFound

class TestDecomposition(TestCase):

    def _print_abs_states(self, got):
        logger = logging.getLogger(__name__)
        logger.info("RESULT:")

        for abs_state in got:
            abs_state_str = "p(x) := "
            for pred in abs_state:
                abs_state_str += " %s" % pred.serialize()
            logging.info(abs_state_str)

    def _eq_sets(self, got, expected):
        new_exp = set()
        for s in expected:
            new_exp.add(frozenset(s))
        same = got == new_exp

        if not same:
            self._print_abs_states(got)
        return same

    def _eq_wformula(self, got, expected):
        solver = _get_solver()
        formula = _set_to_formula(expected)
        same = solver.is_valid(Iff(got, formula))
        return same

    def test_get_neighbors(self):
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]

        r0 = Real(0)
        poly = [x, y]

        tc = [
            # (x<0,y<0) -> [(x=0,y=0),(x<0,y=0),(x=0,y<0)]
            ({x<r0, y<r0},
             [{Equals(x, r0), Equals(y, r0)},
              {x<r0, Equals(y, r0)},
              {Equals(x, r0), y<r0}]),
            # (x=0,y=0) -> [(x<0,y<0),(x<0,y=0),(x<0,y>0),
            #               (x>0,y<0),(x>0,y=0),(x>0,y>0),
            #               (x=0,y<0),(x=0,y>0)]
            ({Equals(x, r0), Equals(y, r0)},
             [{x<r0,y<r0},
              {x<r0,Equals(y,r0)},
              {x<r0,r0<y},
              {r0<x,y<r0},
              {r0<x,Equals(y,r0)},
              {r0<x,r0<y},
              {Equals(x,r0), y<r0},
              {Equals(x,r0),r0<y},
             ]),
            # (x=0,y<0) -> [(x=0,y=0),(x<0,y<0),(x>0,y<0)]
            ({Equals(x, r0), y<r0},
             [{Equals(x, r0), Equals(y, r0)},
              {x<r0, y<r0},
              {r0<x, y<r0}]),
        ]

        for (abs_state, neighbors) in tc:
            res = _get_neighbors([x,y], abs_state)
            res_set = set([frozenset(s) for s in res])
            neighbors_set = set([frozenset(s) for s in neighbors])

            # print("abs state")
            # print(abs_state)
            # print("Obtained")
            # print(res_set)
            # print("Expected")
            # print(neighbors_set)

            self.assertTrue(res_set == neighbors_set)

    @staticmethod
    def get_test_case_1():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(get_range_from_int([x, y], [(1,2),(1,2)]))

        expected_invar = [{x<r0,y<r0},
                          {x<r0,Equals(y,r0)},
                          {x<r0,r0<y},
                          {Equals(x,r0),y<r0},
                          {r0<x,y<r0}]

        return (dyn_sys, TRUE(),[x,y], init, safe,
                (Result.SAFE,expected_invar))

    @staticmethod
    def get_test_case_2():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [],
                            {x : -(y*y), y : x*x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(2,3), (-1,1)])
        safe = Not(get_range_from_int([x, y], [(0,0),(0,0)]))

        expected_invar = [{(0.0 < x),(y < 0.0)},
                          {(r0 < x),Equals(y,r0)},
                          {(r0 < y),(r0 < x)},
                          {(r0 < y),Equals(x,r0)},
                          {(r0 < y),(x < r0)},
                          {Equals(x,r0),(y < r0)},
                          {(x < r0),(y < r0)},
                          {(x < r0),Equals(y,r0)}]

        return (dyn_sys, TRUE(),[x,y], init, safe,
                (Result.SAFE, expected_invar))

    @staticmethod
    def get_test_case_3():
        x, y = [Symbol(var, REAL) for var in ["x", "y"]]
        dyn_sys = DynSystem([x, y], [], [], {x : -y, y : -x}, {}, False)
        r0 = Real(0)
        init = get_range_from_int([x, y], [(-2,-1), (-2,-1)])
        safe = Not(And(Equals(x,r0),y<r0))
        # (dyn_sys, invar, abstraction, init, safe, expected)
        return (dyn_sys, TRUE(),[x,y], init, safe, (Result.UNKNOWN, []))

    def test_invar_lazy(self):
        test_cases = [TestDecomposition.get_test_case_1(),
                      TestDecomposition.get_test_case_2(),
                      TestDecomposition.get_test_case_3()]

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            (res,invars) = get_invar_lazy_set(dyn_sys, invar, poly, init, safe)

            self.assertTrue(res == expected[0] and self._eq_sets(invars,expected[1]))

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            (res, invars) = get_invar_lazy(dyn_sys, invar, poly, init, safe)

            self.assertTrue(res == expected[0] and self._eq_wformula(invars, expected[1]))

        for t in test_cases:
            (dyn_sys, invar, poly, init, safe, expected) = t

            (res, invars) = dwcl(dyn_sys, invar, poly, init, safe)
            self.assertTrue(res == expected[0] and self._eq_wformula(invars,expected[1]))

    def test_invar_dwcl(self):
        print("test invar dwcl")
        def rf(a,b):
            return Real(Fraction(a,b))

        x, y = [Symbol(var, REAL) for var in ["x", "y"]]

        fx = (rf(-3,2) * x * x +
              rf(-1,2) * x * x * x - y)
        fy = 3 * x - y

        dyn_sys = DynSystem([x, y], [], [],
                            {x : fx, y : fy},
                            {}, False)

        invar = TRUE()
        init = (x*x + rf(1,10) * x  + rf(1,400) +
                y*y + rf(3,100) * y + rf(9,40000)) <= rf(1,5000)

        safe = (rf(49,100)) + x + x * x + y + y * y > 0

        poly = [(
            (rf(366,3125) * (x*x*x*x)) +
            (rf(-5089,200000) * (x*x*x*y)) +
            (rf(-19539,250000) * (x*x*x)) +
            (rf(6907,50000) * (x*x*y*y)) +
            (rf(7757,10000) * (x*x*y)) +
            (rf(13077,10000) * (x*x)) +
            (rf(1,500000) * (x*y*y*y)) +
            (rf(-11411,100000) * (x*y*y)) +
            (rf(-2053,5000) * (x*y)) +
            (rf(1,500000) * (x)) +
            (rf(11777,500000) * (y*y*y*y)) +
            (rf(9201,50000) * (y*y*y)) +
            (rf(25341,50000) * (y*y)) +
            (rf(1,1000000) * (y)) +
            rf(-99997,1000000))]


        try:
            get_solver  = partial(get_mathematica, env=get_env())
            print("Find invar dwc...")
            (res, invars) = dwc(dyn_sys, invar, poly, init, safe, get_solver, get_solver)

            print("Checking invar...")
            solver = get_solver()
            is_invar = lzz(solver, invars, dyn_sys, invars, invar)
            solver.exit()
            self.assertTrue(is_invar)


            print("Find invar dwcl...")
            (res, invars) = dwcl(dyn_sys, invar, poly, init, safe, get_solver, get_solver)
            env = get_env()
            solver = get_solver()
            print("Checking invar...")
            is_invar = lzz(solver, invars, dyn_sys, invars, invar)
            solver.exit()
            self.assertTrue(is_invar)
        except pysmt.exceptions.SolverAPINotFound as e:
            print("Cannot load mathematica...")
            return 0



    def test_invar(self):
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, "invar_inputs")

        env = get_env()
        env.enable_infix_notation = True

        long_tests = ["Wiggins Example 18_1_2",
                      "Forsman Phd Ex 6_1 page 99",
                      "Djaballah Chapoutot Kieffer Bouissou 2015 Ex. 1",
                      "Dai Gan Xia Zhan JSC14 Ex. 2",
                      "Ben Sassi Girard 20104 Moore-Greitzer Jet",
                      "3D Lotka Volterra (III)",
                      "Shimizu Morioka System",
                      "Forsman Phd Ex 6_14 page 119",
                      "Prajna PhD Thesis 2-4-1 Page 31",
                      "Dai Gan Xia Zhan JSC14 Ex. 5",
                      "Bhatia Szego Ex_2_4 page 68",
                      "Collin Goriely page 60",
                      "Hamiltonian System 1",
                      "Strogatz Exercise 6_1_5",
                      "Strogatz Exercise 6_1_9 Dipole",
                      "Strogatz Example 6_8_3",
                      "Locally stable nonlinear system",
                      "Strogatz Example 6_3_2",
                      "Dumortier Llibre Artes Ex. 5_2"]

        long_tests_dwcl = ["Dai Gan Xia Zhan JSC14 Ex. 1"]

        not_supported = ["Nonlinear Circuit Example 1+2 (Tunnel Diode Oscillator)"]
        print("cavallo")

        for invar_file in os.listdir(input_path):
            with open(os.path.join(input_path, invar_file), "r") as json_stream:
                problem_list = importInvar(json_stream, env)
                assert(len(problem_list) == 1)
                for p in problem_list:
                    (problem_name, init, safe, dyn_sys, invariants, predicates) = p

                    if (problem_name in long_tests):
                        print("Skipping %s..." % problem_name)
                        continue
                    if (problem_name in not_supported):
                        print("Skipping %s..." % problem_name)
                        continue
                    if (problem_name in long_tests_dwcl):
                        print("Skipping %s..." % problem_name)
                        continue

                    print("Computing DWCL %s..." % (problem_name))
                    (res, invars) = dwcl(dyn_sys, invariants, predicates, init, safe)
                    print("%s %s: %s" % (problem_name, str(res), str(invars)))

                    if (res == Result.SAFE):
                        solver = Solver(logic=QF_NRA, name="z3")
                        print("Sufficient %s: %s" % (problem_name, str(invars.serialize())))
                        is_unsafe = solver.solve(safe)

                        is_unsafe = solver.solve(And(Not(safe), invars))
                        solver.exit()
                        self.assertFalse(is_unsafe)

                        print("Checking invar for %s: %s" % (problem_name, str(invars)))
                        assert (not invars is None)
                        assert (not init is None)
                        assert (not invariants is None)
                        solver = Solver(logic=QF_NRA, name="z3")
                        # solver = get_mathematica(env)

                        # print("INIT " + str(solver.converter.convert(init)))
                        # print("INVAR " + str(solver.converter.convert(invariants)))
                        # print("Candidate " + str(solver.converter.convert(invars)))
                        # print("ODEs:")
                        # for var,ode in dyn_sys.get_odes().items():
                        #     print("\t" + str(var) + " " + str(solver.converter.convert(ode)))
                        # print(dyn_sys)

                        is_invar = lzz(solver, invars, dyn_sys, init, invariants)
                        solver.exit()
                        self.assertTrue(is_invar)

                    elif (res == Result.UNSAFE):
                        solver = Solver(logic=QF_NRA, name="z3")

                        print("Checking unsafe %s:" % (problem_name))

                        solver.add_assertion(And(init, Not(safe)))
                        is_unsafe = solver.solve()
                        solver.exit()
                        self.assertTrue(is_unsafe)


