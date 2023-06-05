""" Test the stabilization functions"""


import logging
import unittest
import os
from functools import partial, reduce
from fractions import Fraction
import numpy as np

try:
    import unittest2 as unittest
except ImportError:
    import unittest
from unittest import skip

from nose.plugins.attrib import attr

from barrier.test import TestCase

from barrier.serialization.hybrid_serialization import importHSVer

from pysmt.shortcuts import get_env, reset_env

from barrier.lyapunov.stabilization.from_sabbath_to_matrices import get_matrices_from_linear_odes

import sympy as sp

def are_equal_sympy_matrices(A, B):
    if sp.shape(A) != sp.shape(B):
        return False
    breakpoint()
    return (A-B == 0).all()

class TestStability(TestCase):


    def test_get_coefficients_odes(self):
        input_path_npz = self.get_from_path("affine_hybrid_inputs_npz")
        input_path_hyb = self.get_from_path("affine_hybrid_inputs_hyb")

        

        for size in [3,5,10,15,18]:

            # Is there a better way to do this?
            reset_env()
            env = get_env()

            with open(os.path.join(input_path_hyb, f"reformulation_size_{size}.hyb"), "r") as f:
                problem = importHSVer(f, env)
            Acs = []
            bs = []
            
            for index_dyn_system in range(len(problem.ha._locations)):
                (A, b) = get_matrices_from_linear_odes(problem.ha._locations[f"{index_dyn_system}"][1])
                Acs.append(A)
                bs.append(b)
            
            np_data = np.load(os.path.join(input_path_npz, f"variables_size_{size}.npz"))
            
            # np.set_printoptions(precision=2, linewidth=1000)
            # print(sp.sympify(np_data["As_homo"][0]) - Acs[0])
            # print(Acs[0])

            for mode in [0,1]:
                # print(size,'= SIZE')
                # print(mode,'= MODE')
                # print(np_data["As_homo"][mode] - Acs[mode])
                # print(np_data["bs_homo"][mode] - bs[mode])
                # breakpoint()
                self.assertTrue( ((np_data["As_homo"][mode] - Acs[mode]) == np.zeros(np.shape(Acs[mode]))).all() )
                self.assertTrue( ((np_data["bs_homo"][mode] - bs[mode]) == np.zeros(np.shape(bs[mode]))).all())
