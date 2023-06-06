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

from scipy import io

from PI_controller_converter.Reformulate.matlab_to_hybrid_as_json import reformulate_PI

def are_equal_sympy_matrices(A, B):
    if sp.shape(A) != sp.shape(B):
        return False
    breakpoint()
    return (sp.simplify(A-B) == 0).all()

class TestStability(TestCase):


    def test_get_matrix_coefficients_odes(self):
        input_path_npz = self.get_from_path("affine_hybrid_inputs_npz")
        input_path_hyb = self.get_from_path("affine_hybrid_inputs_hyb")

        

        for size in [3,5,10,15,18]:

            # Is there a better way to do this?
            reset_env()
            env = get_env()

            with open(os.path.join(input_path_hyb, f"reformulation_size_{size}.hyb"), "r") as f:
                problem = importHSVer(f, env)
            Acs = []
            
            for index_dyn_system in range(len(problem.ha._locations)):
                (A, b) = get_matrices_from_linear_odes(problem.ha._locations[f"{index_dyn_system}"][1])
                Acs.append(A)
            
            np_data = np.load(os.path.join(input_path_npz, f"variables_size_{size}.npz"))

            for mode in [0,1]:
                self.assertTrue( ((np_data["As_homo"][mode] - Acs[mode]) == np.zeros(np.shape(Acs[mode]))).all() )
                

    def test_get_b_odes(self):
        input_path_npz = self.get_from_path("affine_hybrid_inputs_npz")
        input_path_hyb = self.get_from_path("affine_hybrid_inputs_hyb")

        

        for size in [3,5,10,15,18]:

            # Is there a better way to do this?
            reset_env()
            env = get_env()

            with open(os.path.join(input_path_hyb, f"reformulation_size_{size}.hyb"), "r") as f:
                problem = importHSVer(f, env)
            bs = []
            
            for index_dyn_system in range(len(problem.ha._locations)):
                (A, b) = get_matrices_from_linear_odes(problem.ha._locations[f"{index_dyn_system}"][1])
                bs.append(b)
            
            np_data = np.load(os.path.join(input_path_npz, f"variables_size_{size}.npz"))

            for mode in [0,1]:
                self.assertTrue( ((np_data["bs_homo"][mode] - bs[mode]) == np.zeros(np.shape(bs[mode]))).all())

    def test_reformulate_PI_controller(self):
        for size_system in [3,5,10,15,18]:
            input_path_matlab = self.get_from_path("non_reformulated_affine_systems_matlab")
            HybridSystemMatlab = io.loadmat(os.path.join(input_path_matlab, f"data_to_python_size_{size_system}"))
            input_path_npz = self.get_from_path("affine_hybrid_inputs_npz")

            # We format the loaded data in python files
            num_modes = HybridSystemMatlab["num_modes"][0][0]
            num_variables = HybridSystemMatlab["num_variables"][0][0]
            num_controllers = HybridSystemMatlab["num_controllers"][0][0]
            num_outputs = HybridSystemMatlab["num_outputs"][0][0]
            reference_values = HybridSystemMatlab["reference_values"]
            As = []
            Bs = []
            Cs = []
            KIs = []
            KPs = []
            Guards = []
            for ind_mode in range(num_modes):
                As.append(HybridSystemMatlab[f"A_{ind_mode}"])
                Bs.append(HybridSystemMatlab[f"B_{ind_mode}"])
                Cs.append(HybridSystemMatlab[f"C_{ind_mode}"])
                KIs.append(HybridSystemMatlab[f"KI_{ind_mode}"])
                KPs.append(HybridSystemMatlab[f"KP_{ind_mode}"])
                Guards.append(HybridSystemMatlab[f"Guard_{ind_mode}"])

            # We check if the reformulated system has the same value as before

            for ind_mode in range(num_modes):

                (A_homo, b_homo, C_homo, Guard_homo) = reformulate_PI(As[ind_mode], Bs[ind_mode], Cs[ind_mode], 
                                                                        Guards[ind_mode], KPs[ind_mode], KIs[ind_mode], 
                                                                        num_variables, num_controllers, num_outputs, reference_values)

                np_data = np.load(os.path.join(input_path_npz, f"variables_size_{size_system}.npz"))

                self.assertTrue( ((np_data["As_homo"][ind_mode] -  A_homo) == np.zeros(np.shape(A_homo))).all() )
                self.assertTrue( ((np_data["bs_homo"][ind_mode] -  b_homo) == np.zeros(np.shape(b_homo))).all() )
                self.assertTrue( ((np_data["Cs_homo"][ind_mode] -  C_homo) == np.zeros(np.shape(C_homo))).all() )
                self.assertTrue( ((np_data["Guards_homo"][ind_mode] -  Guard_homo) == np.zeros(np.shape(Guard_homo))).all() )