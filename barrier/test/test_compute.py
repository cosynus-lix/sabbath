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

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    is_valid,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals,
    LE, LT, GE, ForAll, Exists, Pow, Plus, Times, GT
)

from time import sleep
from barrier.test import TestCase
from barrier.system import DynSystem
from barrier.compute_barrier import (is_barrier, barrier_generator)
from barrier.utils import (
    get_range
)

class TestBarrier(TestCase):

    def test_is_barrier_1(self):
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        sys = DynSystem([x1,x2], [], [],
                        {
                            x1 : -x1,
                            x2 : x1 - x2
                        },
                        {})

        init = LT(x1 * x1 + x2 * x2, Real(Fraction(1,4)))
        safe = GE(Real(Fraction(4,1)), x1 * x1 + x2 * x2)
        barrier = Real(Fraction(2,1)) * x1 * x1 + Real(Fraction(2,1)) * x1 * x2 + Real(Fraction(3,1)) * x2 * x2 - Real(Fraction(3,1))

        res = is_barrier(sys, init, safe, barrier)

        self.assertTrue(res)


    def test_is_barrier_2(self):
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        sys = DynSystem([x1,x2], [], [],
                        {
                            x1 : (-Real(Fraction(333,500)) * x2 * x2 * x2 * x2 * x2 +
                                  Real(Fraction(439,200)) * x2 * x2 * x2 -
                                  Real(Fraction(1117,500)) * x2 -
                                  x1),
                            x2 : (Real(Fraction(333,500)) * x2 * x2 * x2 * x2 * x2 -
                                  Real(Fraction(439,200)) * x2 * x2 * x2 +
                                  Real(Fraction(617,500)) * x2 +
                                  x1)
                        },
                        {})

        init = get_range([x1, x2],
                         [(Real(Fraction(0,1)),
                           Real(Fraction(1,2))),
                          (Real(Fraction(0,1)),
                           Real(Fraction(1,2)))])

        safe = LE(x1, Real(Fraction(2,1)))

        barrier = x1 * x1 + x1 * x2 + x2 * x2 - Real(Fraction(119,59))

        res = is_barrier(sys, init, safe, barrier)

        self.assertTrue(res)
        
    def test_barrier_generator_1(self):
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        sys = DynSystem([x1,x2], [], [],
                        {
                            x1 : -x1,
                            x2 : x1 - x2
                        },
                        {})

        init = LT(x1 * x1 + x2 * x2, Real(Fraction(1,4)))
        safe = GE(Real(Fraction(4,1)), x1 * x1 + x2 * x2)
        p= Symbol("p",REAL)
        q = Symbol("q",REAL)
        template = Plus(Times(Real(2),x1,x1),Times(Real(2),x1,x2),Times(p,x2,x2),-Real(4))
        gen_barrier = barrier_generator(sys,init,safe, template)

        # The result must be a barrier
        self.assertTrue(is_barrier(sys, init, safe, gen_barrier))


    @unittest.skip("reason for skipping")
    def test_barrier_generator_2(self):
       
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

        sys = DynSystem([x1,x2], [], [],
                        {
                            x1 : (-Real(Fraction(333,500)) * x2 * x2 * x2 * x2 * x2 +
                                  Real(Fraction(439,200)) * x2 * x2 * x2 -
                                  Real(Fraction(1117,500)) * x2 -
                                  x1),
                            x2 : (Real(Fraction(333,500)) * x2 * x2 * x2 * x2 * x2 -
                                  Real(Fraction(439,200)) * x2 * x2 * x2 +
                                  Real(Fraction(617,500)) * x2 +
                                  x1)
                        },
                        {})
        
        init = get_range([x1, x2],
                         [(Real(Fraction(0,1)),
                           Real(Fraction(1,2))),
                          (Real(Fraction(0,1)),
                           Real(Fraction(1,2)))])

        safe = LE(x1, Real(Fraction(2,1)))

        p1,p2,p3,p4 = [Symbol("p%s" % (i+1), REAL) for i in range(4)]        
        template = x1 * x1 + x1 * x2 + x2 * x2 + p4
        gen_barrier = barrier_generator(sys,init,safe, template)
        

