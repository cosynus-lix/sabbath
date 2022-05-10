""" Test the lyapunov function computation """


import logging
import os
import sys
from functools import partial, reduce
from fractions import Fraction

try:
  import unittest2 as unittest
except ImportError:
  import unittest

from unittest import skip

from nose.plugins.attrib import attr

import barrier.test

import numpy as np

from barrier.test import TestCase, skipIfSOSIsNotAvailable
from barrier.lyapunov.piecewise_quadratic import (
  Affine, LeConst, Edge, NumericAffineHS, PiecewiseQuadraticLF,
  get_ge,
  synth_piecewise_quadratic,
  validate, validate_eq_johansson
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


  def _get_system_3(self):
    """
    System with two modes with the same dynamic
    """

    dimensions = 2
    modes = set([1,2]) # modes

    # just a single dynamic for now
    flow = {
      1 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))],
      2 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))]
    }

    invariant = { 1 : [LeConst(np.array([[1,0],[0,0]]), # x <= 10
                               np.array([10,0]))],
                  2 : [LeConst(np.array([[-1,0],[0,0]]), # x >= 10 | -x <= -10
                               np.array([-10,0]))]}

    g1 = LeConst(np.array([[-1,0],[0,0]]), # x >= 5 | -x <= -5
                 np.array([-5,0]))
    g2 = LeConst(np.array([[1,0],[0,0]]), # x <= 5
                 np.array([5,0]))

    fc = NumericAffineHS.get_frame_for_edge(dimensions)
    edges = [Edge(1, [g1], fc, 2),
             Edge(2, [g2], fc, 1)]

    return NumericAffineHS(modes, dimensions, flow,
                           edges, invariant, False)

  def _get_system_4(self):
    """
    System with two modes with the same dynamic
    and switching on the same surface
    """

    dimensions = 2
    modes = set([1,2]) # modes

    # just a single dynamic for now
    flow = {
      1 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))],
      2 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))]
    }

    invariant = { 1 : [LeConst(np.array([[1,0],[0,0]]), # x <= 10
                               np.array([10,0]))],
                  2 : [LeConst(np.array([[-1,0],[0,0]]), # x >= 10 | -x <= -10
                               np.array([-10,0]))]}

    g1 = LeConst(np.array([[-1,0],[0,0]]), # x >= 10 | -x <= -10
                 np.array([-10,0]))
    g2 = LeConst(np.array([[1,0],[0,0]]), # x <= 10
                 np.array([10,0]))

    fc = NumericAffineHS.get_frame_for_edge(dimensions)
    edges = [Edge(1, [g1,g2], fc, 2),
             Edge(2, [g2,g1], fc, 1)]

    return NumericAffineHS(modes, dimensions, flow,
                           edges, invariant, False)


  def _get_system_5(self):
    """
    System with two modes with different dynamic, different switch
    """

    dimensions = 2
    modes = set([1,2]) # modes

    # just a single dynamic for now
    flow = {
      1 : [Affine(np.array([[-1, 0],[1, -2]]),
                  np.array([0,0]))],
      2 : [Affine(np.array([[-3.830, -0.04182],[0.2848, -1.766]]),
                  np.array([-0.7906,0.5590]))]

    }

    invariant = { 1 : [LeConst(np.array([[1,0],[0,0]]), # x <= 10
                               np.array([10,0]))],
                  2 : [LeConst(np.array([[-1,0],[0,0]]), # x >= 10 | -x <= -10
                               np.array([-10,0]))]}

    g1 = LeConst(np.array([[-1,0],[0,0]]), # x >= 5 | -x <= -5
                 np.array([-5,0]))
    g2 = LeConst(np.array([[1,0],[0,0]]), # x <= 5
                 np.array([5,0]))

    fc = NumericAffineHS.get_frame_for_edge(dimensions)
    edges = [Edge(1, [g1], fc, 2),
             Edge(2, [g2], fc, 1)]

    return NumericAffineHS(modes, dimensions, flow,
                           edges, invariant, False)

  def _get_s5_s_procedure(self, hs):
    m1_invar = np.array([[0,0,-0.5],
                         [0,0,0],
                         [-0.5,0,10]])
    m2_invar = np.array([[0,0,0.5],
                         [0,0,0],
                         [0.5,0,-10]])

    m1_m2_invar = np.array([[0,0,0.5],
                            [0,0,0],
                            [0.5,0,5]])
    m2_m1_invar = np.array([[0,0,-0.5],
                            [0,0,0],
                            [-0.5,0,5]])

    hs.set_s_procedure_invar(1, [m1_invar])
    hs.set_s_procedure_invar(2, [m2_invar])

    hs.set_s_procedure_edge(0, [m1_m2_invar])
    hs.set_s_procedure_edge(1, [m2_m1_invar])

    assert hs.verify_s_procedure()
    return hs


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


  def _get_miniAEC(self):
    dimensions = 4
    modes = set([1,2])

    # Constant from the problem
    C = np.array([[0.00182850, 0, 0],
                  [0.0000102703, 0.0000308108, 0],
                  [-0.00177778, 0, 0],
                  [0, 0.00359591, 0]])
    refval = np.array([0.5,5,-1,20]) # reference value
    Theta = 1 # switch threshold

    A1 = np.array([[-3.82987000e+00, -4.18250000e-02, -1.01908000e+03,  0.00000000e+00],
                   [ 2.84779000e-01, -1.76641000e+00, -3.49432000e+02,  0.00000000e+00],
                   [ 0.00000000e+00,  0.00000000e+00, -6.25000000e+01, -7.90569000e-01],
                   [-1.12820827e-02,  7.64770125e-05,  1.86338778e+00,  0.00000000e+00]])
    b1 = np.array([0.,0.,0.,5.])
    A2 = np.array([[-3.82987000e+00, -4.18250000e-02, -1.01908000e+03, 0.00000000e+00],
                   [2.84779000e-01, -1.76641000e+00, -3.49432000e+02, 0.00000000e+00],
                   [0.00000000e+00, 0.00000000e+00, -6.25000000e+01, -7.90569000e-01],
                   [-1.74846355e-03, -5.61361939e-03, 2.12325368e-01, 0.00000000e+00]])
    b2 = np.array([0.,0.,0.,1000.])
    flow = {
      1 : [Affine(A1,b1)],
      2 : [Affine(A2,b2)]
    }

    zero_matrix = np.zeros((dimensions,dimensions))
    zero_array = np.zeros(dimensions)
    def _copy_and_set(m, vals):
      m_copy = np.copy(m)
      for (i,j,val) in vals:
        m_copy[i][j] = val 
      return m_copy

    # (refval[0] - Theta) / C[0,0]
    refval_const = (refval[0] - Theta) / C[0,0]
    # x[0] >= refval_const
    v = zero_array.copy()
    v[0] = refval_const
    m1_invar = [get_ge(_copy_and_set(zero_matrix, [(0,0,1)]),v)]
    # x[0] <= refval_const
    m2_invar = [LeConst(_copy_and_set(zero_matrix, [(0,0,1)]),v)]
    invariant = {1 : m1_invar, 2 : m2_invar}

    print(m1_invar)

    # x[0] >= refval_const and x[0] <= refval_const
    guard = m1_invar + m2_invar
    # No update
    frame_update = Affine(np.identity(dimensions),np.zeros(dimensions))
    edges = [
      Edge(1, guard, frame_update, 2),
      Edge(2, guard, frame_update, 1)
    ]
    hs = NumericAffineHS(modes, dimensions, flow, edges, invariant, False)


    return hs

  def _get_miniAEC_s_procedure(self, hs):
    # S-Procedure for invariants and guards
    A1 = hs.flows[1][0].A

    C = np.array([[0.00182850, 0, 0],
                  [0.0000102703, 0.0000308108, 0],
                  [-0.00177778, 0, 0],
                  [0, 0.00359591, 0]])
    refval = np.array([0.5,5,-1,20]) # reference value
    Theta = 1 # switch threshold

    a = 0.000914255
    # 2 a x0 + 1/2
    m1_invar = [np.array([[0,0,0,0,a],
                          [0,0,0,0,0],
                          [0,0,0,0,0],
                          [0,0,0,0,0],
                          [a,0,0,0,0.55]])]

    # Q_2 = -Q_1
    m2_invar = [np.array([[0,0,0,0,-a],
                          [0,0,0,0,0],
                          [0,0,0,0,0],
                          [0,0,0,0,0],
                          [-a,0,0,0,-0.5]])]

    vv = np.array([np.concatenate([[0], np.delete(A1[0],0)])])
    R12 = np.vstack([
      np.hstack([np.zeros([4,4]), np.transpose(vv)]),
      np.hstack([vv, [[A1[0,0] * (-(Theta - refval[0])/C[0,0])]]])
    ])
    R21 = - R12

    m1_m2_guard = [R12]
    m2_m1_guard = [-R12]

    hs.make_homogeneous()

    hs.set_s_procedure_invar(1, m1_invar)
    hs.set_s_procedure_invar(2, m2_invar)
    hs.set_s_procedure_edge(0, m1_m2_guard)
    hs.set_s_procedure_edge(1, m2_m1_guard)

    return hs

  def test_s1(self):
    hs = self._get_system_1()
    hs.make_homogeneous()
    (res, lf) = synth_piecewise_quadratic(hs,epsilon=0.1,dbg_stream=sys.stderr)
    self.assertTrue(res)
    self.assertTrue(validate(hs, lf))

  def test_s2(self):
    hs = self._get_system_2()
    hs.make_homogeneous()
    epsilon=0.00000001
    (has_function, lf) = synth_piecewise_quadratic(hs,epsilon=epsilon,dbg_stream=sys.stderr)

    print(lf)

    self.assertTrue(has_function)
    self.assertTrue(validate(hs, lf))

  def test_s3(self):
    hs = self._get_system_3()
    hs.make_homogeneous()
    # can still find a common lyapunov
    (res, lf) = synth_piecewise_quadratic(hs,dbg_stream=sys.stderr)
    self.assertTrue(res)
    self.assertTrue(validate(hs, lf))

  def test_s4(self):
    hs = self._get_system_4()
    hs.make_homogeneous()
    # can still find a common lyapunov
    (res, _) = synth_piecewise_quadratic(hs,dbg_stream=sys.stderr)
    self.assertTrue(res)
    (res, lf) = synth_piecewise_quadratic(hs,modes_in_loop=[(1,2)],dbg_stream=sys.stderr)
    self.assertTrue(res)
    self.assertTrue(validate(hs, lf))

  def test_s5(self):
    hs = self._get_system_5()
    hs.make_homogeneous()

    hs = self._get_s5_s_procedure(hs)

    (found_lyap, lf) = synth_piecewise_quadratic(hs,dbg_stream=sys.stderr)
    self.assertTrue(found_lyap)
    self.assertTrue(validate(hs, lf))


  def test_3_8(self):
    hs = self._get_system_3_8()
    self.assertTrue(hs.is_homogeneous)
    self.assertTrue(hs.verify_s_procedure())
    (res, lf) = synth_piecewise_quadratic(hs, epsilon=0.01000158, dbg_stream=sys.stderr)
    self.assertTrue(res)
    # still does not work on edges
    self.assertTrue(validate(hs, lf))


  @unittest.skip("To fix the encoding of equalities")
  def test_miniAEC(self):
    hs = self._get_miniAEC()
    hs = self._get_miniAEC_s_procedure(hs)
    self.assertTrue(hs.is_homogeneous)
    self.assertTrue(hs.verify_s_procedure())
    (found_lyapunov, lf) = synth_piecewise_quadratic(hs, epsilon=0.00001, modes_in_loop=[(1,2)], dbg_stream=sys.stderr)
    self.assertTrue(found_lyapunov)
    self.assertTrue(validate(hs, lf))

  def test_validate_miniAEC_johansson(self):
    hs = self._get_miniAEC()
    # Change the coordinates of hs with respect to the equlibrium point in m1
    flow_m1 = hs.flows[1][0]
    # equivalent to np.linalg.solve(A,-b)
    eq_m1 = -1 * np.dot(np.linalg.inv(flow_m1.A),flow_m1.b)
    print(eq_m1)

    print(hs)
    hs.change_coordinate(eq_m1) # change the coordinate system
    print(hs)

    hs.make_homogeneous()

    lf = PiecewiseQuadraticLF()
    lf.alpha = 2.2970197526097653e-06
    I_tilda = np.identity(hs.dimensions)
    I_tilda[hs.dimensions-1][hs.dimensions-1] = 0
    lf.I_tilda = {
      1 : I_tilda,
      2 : I_tilda
    }
    lf.lyapunov_map = {
      1 : np.array([[ 7.66748610e-05, -5.64847156e-05, -1.30257340e-03, -1.02411004e-04, 0],
                    [-5.64847156e-05,  5.51612026e-05,  7.42557294e-04,  3.47754299e-05, 0],
                    [-1.30257340e-03,  7.42557294e-04,  1.00118857e-01,  3.34687137e-03, 0],
                    [-1.02411004e-04,  3.47754299e-05,  3.34687137e-03,  3.87594687e-04, 0],
                    [0, 0, 0, 0, 0]]),
      2 : np.array([[ 8.40356200e-05, -5.73622057e-05, -1.29238642e-03, -1.23657314e-04, -9.16253756e-03],
                    [-5.73622057e-05,  5.51612026e-05,  7.42557294e-04,  3.47754299e-05, -4.79896140e-04],
                    [-1.29238642e-03,  7.42557294e-04,  1.00118857e-01,  3.34687137e-03, 5.57122380e-03],
                    [-1.23657314e-04,  3.47754299e-05,  3.34687137e-03,  3.87594687e-04, -1.16195298e-02],
                    [-9.16253756e-03, -4.79896140e-04,  5.57122380e-03, -1.16195298e-02, -1.22234878e+01]])
    }

    lf.lyapunov_map = {
        1 : np.array([[ 1.92e-04, -1.41e-04, -3.25e-03, -2.58e-04, 0],
                      [-1.41e-04,  1.36e-04,  1.87e-03,  9.27e-05, 0],
                      [-3.25e-03,  1.87e-03,  2.42e-01,  8.21e-03, 0],
                      [-2.58e-04,  9.27e-05,  8.21e-03,  9.49e-04, 0],
                      [0,0,0,0,0]]),
        2 : np.array([[ 2.09e-04, -1.43e-04, -3.21e-03, -3.10e-04, -2.12e-02],
                      [-1.43e-04,  1.36e-04,  1.87e-03,  9.27e-05, -7.70e-04],
                      [-3.21e-03,  1.87e-03,  2.42e-01,  8.21e-03,  1.88e-02],
                      [-3.10e-04,  9.27e-05,  8.21e-03,  9.49e-04, -2.89e-02],
                      [-2.12e-02, -7.70e-04,  1.88e-02, -2.89e-02, -2.83e+01]])
    }

    self.assertTrue(validate_eq_johansson(hs, lf))

  def test_app(self):
    flow = Affine(np.array([[-3.83,    -0.04182, -0.7906 ],
                            [ 0.2848,  -1.766,    0.559  ],
                            [ 0.,       0.,       0.     ]]),
                  np.zeros(3))
    hs = NumericAffineHS([1], 3, {1 : [flow]}, [], {1 : []}, True)

    lf = PiecewiseQuadraticLF()
    app = np.concatenate((np.identity(2),np.zeros((2,1))), axis = 1)
    I_tilda = np.concatenate((app,np.zeros((1,3))), axis = 0)
    lf.I_tilda = {
      1 : I_tilda,
    }
    lf.alpha = 3.888063241253907e-08
    lf.beta = 1.0
    lf.gamma = 0.17378531357276597
    lf.lyapunov_map = {
        1 : np.array([[ 0.41665144,  0.05090385,  0.07289088],
                      [ 0.05090385,  0.65000279, -0.17312401],
                      [ 0.07289088, -0.17312401,  1.09345671]])
    }

    self.assertTrue(validate(hs, lf))
