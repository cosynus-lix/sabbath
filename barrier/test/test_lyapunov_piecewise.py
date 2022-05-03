""" Test the lyapunov function computation """


import logging
import unittest
import os
import sys
from functools import partial, reduce
from fractions import Fraction

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from nose.plugins.attrib import attr



import barrier.test

import numpy as np

from barrier.test import TestCase, skipIfSOSIsNotAvailable
from barrier.lyapunov.piecewise_quadratic import (
  Affine, LeConst, Edge, NumericAffineHS,
  synth_piecewise_quadratic,
  validate
)


class TestLyapunovPiecewise(TestCase):

  def _get_system_1(self):
    dimensions = 2 # number of continuous variables
    modes = set([1]) # modes

    # just a single dynamic for now
    flow = {
      1 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))]
    }
    edges = []
    invariant = { 1 : [] }

    return NumericAffineHS(modes, dimensions, flow,
                           edges, invariant, False)

  def _get_system_2(self):
    dimensions = 2 # number of continuous variables
    modes = set([1]) # modes

    # just a single dynamic for now
    flow = {
      1 : [Affine(np.array([[-3.830, -0.04182],[0.2848, -1.766]]),
                  np.array([-0.7906,0.5590]))]
    }
    edges = []
    invariant = { 1 : [] }

    return NumericAffineHS(modes, dimensions, flow, edges, invariant, False)


  def _get_system_3_8(self):
    """
    Note: we pick a single constraint inn the differential inclusion for now.

    If it's stable with the differential inclusion, then it's stablle in the simpler case.

    """
    dimensions = 2 # number of continuous variables
    modes = set([1,2,3]) # modes
    flow = {
      1 : [Affine(np.array([[0,0],[0,0]]),
                  np.array([0,-1.95]))],
      2 : [Affine(np.array([[0,1],[-0.000975,-0.0507]]),
                  np.array([0,0.0]))],
      3 : [Affine(np.array([[0,0],[0,0]]),
                  np.array([0,1.425]))],
    }

    # m1: 5 <= v <= 20 & -500 <= x <= 500
    m1_invar = [LeConst(np.array([[1,0],[0,1]]),np.array([500,20])),
                LeConst(np.array([[-1,0],[0,-1]]),np.array([500,-5]))]
    # m2: -15 <= v <= 15 & -500 <= x <= 500
    m2_invar = [LeConst(np.array([[1,0],[0,1]]),np.array([500,15])),
                LeConst(np.array([[-1,0],[0,-1]]),np.array([500,15]))]
    # m3: -20 <= v <= -5 & -500 <= x <= 500
    m3_invar = [LeConst(np.array([[1,0],[0,1]]),np.array([500,-5])),
                LeConst(np.array([[-1,0],[0,-1]]),np.array([500,20]))]
    invariant = {1 : m1_invar, 2 : m2_invar, 3 : m3_invar}

    frame_update = Affine(np.identity(dimensions),np.zeros(dimensions))
    reset_x = np.identity(dimensions)
    reset_x[0,0] = 0
    reset_x_update = Affine(reset_x, np.zeros(dimensions))
    edges = [
      Edge(1, [LeConst(np.array([[0,0],[0,1]]),np.array([0,7]))], reset_x_update, 2), # m1 -> m2, v <= 7
      Edge(2, [LeConst(np.array([[0,0],[0,-1]]),np.array([0,-12]))], frame_update, 1), # m1 -> m2, v >= 12
      Edge(2, [LeConst(np.array([[0,0],[0,1]]),np.array([0,-12]))], frame_update, 3), # m2 -> m3, v <= -12
      Edge(3, [LeConst(np.array([[0,0],[0,-1]]),np.array([0,7]))], reset_x_update, 2), # m3 -> m2, v >= -7
    ]

    hs = NumericAffineHS(modes, dimensions, flow, edges, invariant, False)
    # need to make the system homogeneous to apply the S-procedure
    hs.make_homogeneous()

    # S-Procedure for invariants and guards
    m1_invar = np.array([[0,0,0],
                         [0,-0.008899,0.111111],
                         [0,0.111111,-0.388889]])
    m3_invar = np.array([[0,0,0],
                         [0,-0.008899,-0.111111],
                         [0,-0.111111,-0.388889]])
    m2_invar = np.array([[0.000002,0,0],
                         [0,-0.002222,0],
                         [0,0,1]])
    # e3: m1 -> m2
    m1_m2_guard = np.array([[-0.000002,0,0],
                            [0,-0.5,3],
                            [0,3,-17]])

    # e2 contains in [-20,-12] m2 -> m3
    m2_m3_guard = np.array([[-0.000002,0,0],
                            [0,-0.222222,-3],
                            [0,-3,-39.5]])

    # e1 contains in [-5,-7]
    m3_m2_guard = np.array([[-0.000002,0,0],
                            [0,-0.5,-3],
                            [0,-3,-17]])

    # e4
    m2_m1_guard = np.array([[-0.000002,0,0],
                            [0,-0.222222,3],
                            [0,3,-39.5]])

    hs.set_s_procedure_invar(1, [m1_invar])
    hs.set_s_procedure_invar(2, [m2_invar])
    hs.set_s_procedure_invar(3, [m3_invar])
    hs.set_s_procedure_edge(0, [m1_m2_guard])
    hs.set_s_procedure_edge(1, [m2_m1_guard])
    hs.set_s_procedure_edge(2, [m2_m3_guard])
    hs.set_s_procedure_edge(3, [m3_m2_guard])
    assert hs.verify_s_procedure()
    return hs


  def test_s1(self):
    hs = self._get_system_1()
    hs.make_homogeneous()
    (res, lf) = synth_piecewise_quadratic(hs,dbg_stream=sys.stderr)
    self.assertTrue(res)
    # self.assertTrue(validate(hs, lf))

  def test_s2(self):
    hs = self._get_system_2()
    hs.make_homogeneous()
    (res, _) = synth_piecewise_quadratic(hs,dbg_stream=sys.stderr)
    self.assertFalse(res)

  def test_3_8(self):
    hs = self._get_system_3_8()
    hs.make_homogeneous()
    (res, lf) = synth_piecewise_quadratic(hs, 0.01000158, dbg_stream=sys.stderr)
    self.assertTrue(res)
    validate(hs, lf)
