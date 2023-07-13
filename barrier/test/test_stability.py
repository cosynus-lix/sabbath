"""
WARNING: Test cases calls the LMI solver, which is somehow non-deterministic (maybe there is a seed to set). So, some tests may fail depending on the LMI result (still did not happened)

"""

import sys


from functools import partial
from fractions import Fraction

from pysmt.typing import REAL
from pysmt.logics import QF_NRA
from pysmt.shortcuts import *

from barrier.mathematica.mathematica import (
    get_mathematica, exit_callback_print_time, MathematicaSession
)

from barrier.system import DynSystem
from barrier.lyapunov.la_smt import matrix_times_vect

from stability_hs import (
    Config, GASOptions,
    get_gas_lyapunov,
    compute_lyapunov,
    find_inward_region,
    find_level_set,
    find_stability_assumption,
    verify_stability_dyn_system,
    # sample_stability_aux,
    Result
)

from . import TestCase

from nose.plugins.attrib import attr

class TestVerifyPO(TestCase):
    @attr('mathematica')
    def tearDown(self):
        MathematicaSession.terminate_session()


    def _get_gas_options(self):
        # Use sdp for the test, this should be fixed.
        return GASOptions(False, False, False, True, False, False, False, True, 'cvxopt', True, False, False, 'smt')

    def test_lyapunov_gas(self):
        """
        To be moved in barrier.
        """

        gas_opts = self._get_gas_options()

        var = [Symbol("x%s" % (i+1), REAL) for i in range(10)]

        # List of systems to test
        test_cases = [
            # [-1 0] [1 -2]
            ([[Real(-1),Real(0)], [Real(1),Real(-2)]], True),
            # [1 0] [0 -1]
            ([[Real(1),Real(0)], [Real(0),Real(-1)]], False),
            # Test spiral system
            ([[Real(1),Real(4)], [Real(-2),Real(-5)]], True),
            # Test spiral system
            ([[Real(-0.5),Real(-2)], [Real(2),Real(-0.2)]], True),
        ]

        for (matrix, exp_is_stable) in test_cases:
            states = [var[i] for i in range(len(matrix))]
            odes_vec = matrix_times_vect(states,
                                         matrix)
            odes = {var[i] : odes_vec[i] for i in range(len(matrix))}

            sys = DynSystem(states, [], [],
                            odes,
                            {})

            lyap = get_gas_lyapunov(sys, partial(Solver, logic=QF_NRA, name="z3"),gas_opts)
            is_stable = not lyap is None

            if is_stable and False: # Debug print
                print(lyap.serialize())

            self.assertTrue(exp_is_stable == is_stable)

    def test_lyapunov_gas_rescaled(self):
        """
        To be moved in barrier.
        """
        gas_opts = self._get_gas_options()

        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        sys = DynSystem([x,y], [], [],
                        {x : x * Real(-1) + Real(1),
                         y : x + y * Real(-2) + Real(2)},
                        {})
        (is_stable, eq_point, lp) = compute_lyapunov(sys, partial(Solver, logic=QF_NRA, name="z3"),gas_opts)
        self.assertTrue(is_stable and not lp is None)

        # print("LYAPUNOV ", sys.get_derivator().simplify(lp).serialize(), "\n", eq_point)



    def test_inward_region(self):
        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        # [[-1 0] [1 -2]] A + [1 2]
        sys = DynSystem([x,y], [], [],
                        {x : x * Real(-1) + Real(1),
                         y : x + y * Real(-2) + Real(2)},
                        {})
        # x - 2 
        switching_pred = x - Real(2)

        region = find_inward_region(sys, switching_pred)

        self.assertTrue(is_valid(Iff(region,
                                     And(Equals(switching_pred,Real(0)),
                                         LT(Minus(Real(1), x), Real(0))))))


    def test_find_level_set(self):
        x = Symbol('x', REAL)
        y = Symbol('y', REAL)

        c1 = Real(Fraction(5457907/4000000))
        c2 = Real(Fraction(-988373,1000000))
        c3 = Real(Fraction(-623197,500000))
        c4 = Real(Fraction(282783,1000000))
        c5 = Real(Fraction(518179,1000000))
        c6 = Real(Fraction(17503,125000))
        lyap = (c1 + (c2 * y) + (c3*x) + (c4* (y*y)) + (c5 * (x*x)) + (c6 * x *y))

        get_z3 = partial(Solver, logic=QF_NRA, name="z3")
        config = Config(get_z3)

        # Test finding the approximate max (it's 50)
        delta = Fraction(1,10)
        res = find_level_set(config, lyap, TRUE(), LT(lyap, Real(50)),
                             delta)
        self.assertTrue(get_z3().is_sat(Implies(LE(lyap, Minus(Real(50), Real(delta))),
                                                res)))

        # Test finding True
        res = find_level_set(config, lyap, Equals(x, Real(2)), Equals(x, Real(2)), delta)
        self.assertTrue(TRUE() == res)


        # Test spiral system
        c1 = 779281/1000000
        c2 = 511643/1000000
        c3 = 257013/500000
        lyap_spiral = ((x * ((x * c1) + (y * c2))) + (y * ((x * c2) + (y * c3))))

        res = find_level_set(config, lyap_spiral,
                             Equals(x,Real(2)),
                             And(Equals(x,Real(2)),
                                 LT(x + Real(4) * y, Real(0))),
                             delta)
        self.assertTrue(get_z3().is_sat(Implies(LE(lyap, Minus(Real(Fraction(35/16)), Real(delta))),
                                                res)))




    def t1(self):
        """
        Two identical systems, stable.
        """
        get_z3 = partial(Solver, logic=QF_NRA, name="z3")
        config = Config(get_z3)

        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        sys = DynSystem([x,y], [], [],
                        {x : x * Real(-1) + Real(1),
                         y : x + y * Real(-2) + Real(2)},
                        {})

        assumptions = find_stability_assumption(config,
                                                [sys,sys],
                                                Minus(x,Real(2)))
        self.assertTrue(get_z3().is_valid(assumptions))


    def t2(self):
        """
        Two systems, both stable.
        Eq point in m0
        """
        get_z3 = partial(Solver, logic=QF_NRA, name="z3")
        config = Config(get_z3)

        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        s1 = DynSystem([x,y], [], [],
                       {x : x * Real(-1) + Real(1),
                        y : x + y * Real(-2) + Real(2)},
                       {})

        s2 = DynSystem([x,y], [], [],
                       {x : x * Real(-1) + Real(-2),
                        y : x + y * Real(-2) + Real(-5)},
                       {})

        assumptions = find_stability_assumption(config,
                                                [s1,s2],
                                                Minus(x,Real(2)))
        self.assertTrue(get_z3().is_valid(assumptions))

    def t3(self):
        """
        Two systems, both stable.
        m0 spiral, m1 not.
        Eq points both in m0
        """
        get_z3 = partial(Solver, logic=QF_NRA, name="z3")
        config = Config(get_z3)

        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        s0 = DynSystem([x,y], [], [],
                       # x + 4y
                       {x : x * Real(1)  + y * Real(4),
                        # -2x - 5y
                        y : x * Real(-2) + y * Real(-5)},
                       {})

        s1 = DynSystem([x,y], [], [],
                       {
                           # -(x - 0.5) + 1
                           x : Minus(Real(0), Minus(x, Real(0.5))) + 1,
                           # (x - 0.5) - 2*(y + 3) + 2}
                           y : Minus(x, Real(0.5)) + Minus(Real(0), Real(2) * (y + Real(3))) + Real(2)
                        }, 
                       {})

        assumptions = find_stability_assumption(config,
                                                [s0,s1],
                                                Minus(x,Real(2)))

        # Don't really know the result - depends on lyapunov function computation.
        # just check it's not empty and hope for the best
        self.assertTrue(get_z3().is_sat(assumptions))

    @attr('mathematica')
    def test_verify_stability_mathematica(self):
        get_z3 = partial(Solver, logic=QF_NRA, name="z3")

        # Test:
        exit_callback_inst = partial(exit_callback_print_time, outstream=sys.stdout)
        get_z3 = partial(get_mathematica,
                         budget_time=0,
                         env=get_env(),
                         exit_callback=exit_callback_inst)

        config = Config(get_z3)


        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        s0 = DynSystem([x,y], [], [],
                       # x + 4y
                       {x : x * Real(1)  + y * Real(4),
                        # -2x - 5y
                        y : x * Real(-2) + y * Real(-5)},
                       {})

        s1 = DynSystem([x,y], [], [],
                       {
                           # -(x - 0.5) + 1
                           x : Minus(Real(0), Minus(x, Real(0.5))) + 1,
                           # (x - 0.5) - 2*(y + 3) + 2}
                           y : Minus(x, Real(0.5)) + Minus(Real(0), Real(2) * (y + Real(3))) + Real(2)
                        }, 
                       {})

        stable_points = [
            # First case
#            {x : Real(0), y : Real(0)},
#            {x : Real(-2), y : Real(2)},
#            {x : Real(1), y : Real(-2)},
            # Second case
            {x : Real(2.2), y : Real(-2)},
            # 
            {x : Real(0.01), y : Real(0.01)},
        ]

        unknown_stable_points = [
            {x : Real(-2), y : Real(-2)},
            {x : Real(1), y : Real(2)},
            # Second case
            {x : Real(4), y : Real(0)},
            {x : Real(3), y : Real(0)},
        ]

        gas_opts = [self._get_gas_options(), self._get_gas_options()]

        for s in stable_points:
            self.assertTrue(Result.STABLE == verify_stability_dyn_system(config, [s0,s1], Minus(x,Real(2)), s, gas_opts))
            # Test inversion
            self.assertTrue(Result.STABLE == verify_stability_dyn_system(config, [s1,s0], Minus(Real(2),x), s, gas_opts))


        for s in unknown_stable_points:
            self.assertTrue(Result.UNKNOWN == verify_stability_dyn_system(config, [s0,s1], Minus(x,Real(2)), s, gas_opts))
            # test inversion
            self.assertTrue(Result.UNKNOWN == verify_stability_dyn_system(config, [s1,s0], Minus(Real(2),x), s, gas_opts))


    def test_verify_stability(self):
        get_z3 = partial(Solver, logic=QF_NRA, name="z3")

        config = Config(get_z3)

        x,y = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        s0 = DynSystem([x,y], [], [],
                       # x + 4y
                       {x : x * Real(1)  + y * Real(4),
                        # -2x - 5y
                        y : x * Real(-2) + y * Real(-5)},
                       {})

        s1 = DynSystem([x,y], [], [],
                       {
                           # -(x - 0.5) + 1
                           x : Minus(Real(0), Minus(x, Real(0.5))) + 1,
                           # (x - 0.5) - 2*(y + 3) + 2}
                           y : Minus(x, Real(0.5)) + Minus(Real(0), Real(2) * (y + Real(3))) + Real(2)
                        }, 
                       {})

        stable_points = [
            # First case
#            {x : Real(0), y : Real(0)},
#            {x : Real(-2), y : Real(2)},
#            {x : Real(1), y : Real(-2)},
            # Second case
            {x : Real(2.2), y : Real(-2)},
            # 
            {x : Real(0.01), y : Real(0.01)},
        ]

        unknown_stable_points = [
            {x : Real(-2), y : Real(-2)},
            {x : Real(1), y : Real(2)},
            # Second case
            {x : Real(4), y : Real(0)},
            {x : Real(3), y : Real(0)},
        ]

        gas_opts = [self._get_gas_options(), self._get_gas_options()]

        for s in stable_points:
            self.assertTrue(Result.STABLE == verify_stability_dyn_system(config, [s0,s1], Minus(x,Real(2)), s, gas_opts))
            # Test inversion
            self.assertTrue(Result.STABLE == verify_stability_dyn_system(config, [s1,s0], Minus(Real(2),x), s, gas_opts))


        for s in unknown_stable_points:
            self.assertTrue(Result.UNKNOWN == verify_stability_dyn_system(config, [s0,s1], Minus(x,Real(2)), s, gas_opts))
            # test inversion
            self.assertTrue(Result.UNKNOWN == verify_stability_dyn_system(config, [s1,s0], Minus(Real(2),x), s, gas_opts))
