""" Test the stabilization functions"""

import os

import numpy as np

import sympy as sp
from pysmt.shortcuts import get_env, reset_env
from scipy import io

from sabbath.stability.from_sabbath_to_matrices import \
    get_matrices_from_linear_odes
from sabbath.serialization.hybrid_serialization import importHSVer
from sabbath.test import TestCase

from utils.reformulate_PI_controller.matlab_to_hybrid_as_json import \
    reformulate_PI


def are_equal_sympy_matrices(A, B):
    if sp.shape(A) != sp.shape(B):
        return False
    breakpoint()
    return (sp.simplify(A-B) == 0).all()

class TestPIConverter(TestCase):


    def test_get_matrix_coefficients_odes(self):
        input_path_npz = os.path.dirname(os.path.abspath(__file__))+"/affine_hybrid_inputs_npz"
        input_path_hyb = os.path.dirname(os.path.abspath(__file__))+"/affine_hybrid_inputs_hyb"



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
        input_path_npz = os.path.dirname(os.path.abspath(__file__))+"/affine_hybrid_inputs_npz"
        input_path_hyb = os.path.dirname(os.path.abspath(__file__))+"/affine_hybrid_inputs_hyb"



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
            input_path_matlab = os.path.dirname(os.path.abspath(__file__))+"/non_reformulated_affine_systems_matlab"
            HybridSystemMatlab = io.loadmat(os.path.join(input_path_matlab, f"data_to_python_size_{size_system}"))
            input_path_npz = os.path.dirname(os.path.abspath(__file__))+"/affine_hybrid_inputs_npz"

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
            Invars_geq0 = []
            for ind_mode in range(num_modes):
                As.append(HybridSystemMatlab[f"A_{ind_mode}"])
                Bs.append(HybridSystemMatlab[f"B_{ind_mode}"])
                Cs.append(HybridSystemMatlab[f"C_{ind_mode}"])
                KIs.append(HybridSystemMatlab[f"KI_{ind_mode}"])
                KPs.append(HybridSystemMatlab[f"KP_{ind_mode}"])
                Invars_geq0.append(HybridSystemMatlab[f"Invar_{ind_mode}_geq0"])

            # We check if the reformulated system has the same value as before

            for ind_mode in range(num_modes):

                (A_homo, b_homo, C_homo, Invar_geq0_homo) = reformulate_PI(As[ind_mode], Bs[ind_mode], Cs[ind_mode],
                                                                        Invars_geq0[ind_mode], KPs[ind_mode], KIs[ind_mode],
                                                                        num_variables, num_controllers, num_outputs, reference_values)

                np_data = np.load(os.path.join(input_path_npz, f"variables_size_{size_system}.npz"))

                # The failing of the test could be due to numerical reasons.
                # The algorithm involved in the multiplication of the matrices can change the result.
                # Check the magnitude of the error in case this does not work (10^-10 cold not be enough, maybe).
                self.assertTrue( np.linalg.norm((np_data["As_homo"][ind_mode] -  A_homo)) / np.linalg.norm(np_data["As_homo"][ind_mode]) < 1e-10 )
                self.assertTrue( np.linalg.norm((np_data["bs_homo"][ind_mode] -  b_homo)) / np.linalg.norm(np_data["bs_homo"][ind_mode]) < 1e-10 )
                self.assertTrue( np.linalg.norm((np_data["Cs_homo"][ind_mode] -  C_homo)) / np.linalg.norm(np_data["Cs_homo"][ind_mode]) < 1e-10 )
                self.assertTrue( np.linalg.norm((np_data["Invars_geq0_homo"][ind_mode] -  Invar_geq0_homo)) / np.linalg.norm(np_data["Invars_geq0_homo"][ind_mode]) < 1e-10 )
