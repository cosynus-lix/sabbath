""" Verify stability of a hybrid system
"""

import sys
import argparse
import logging
import os
import signal
import sys

from barrier.lzz.lzz import LzzOpt
from barrier.serialization.hybrid_serialization import importHSVer
from barrier.decomposition.predicates import AbsPredsTypes, get_polynomials_ha
from barrier.decomposition.encoding import (
    DecompositionOptions, DecompositionEncoderHA
)
from barrier.decomposition.utils import get_unique_poly_list
from barrier.lyapunov.piecewise_affine_case import *


from pysmt.shortcuts import (
    get_env
)

from functools import partial

from barrier.lyapunov.stabilization.from_sabbath_to_matrices import  build_dyn_systems_from_hs_file

# These are for the SMT solvers
from barrier.utils import get_cvc5_smtlib, get_mathsat_smtlib
from barrier.mathematica.mathematica import (
    get_mathematica, exit_callback_print_time, OutOfTimeSolverError, MathematicaSession
)

import argparse
import json
import os
import functools
from enum import Enum
import time

try:
    import reformulate
    import svl_single_mode
    from serialization import serializeSynthesis, importSynthesis
except:
    # Dirty trick to get around the current structure
    # and still have tests.
    from . import reformulate
    from . import svl_single_mode
    from .serialization import serializeSynthesis, importSynthesis

import sys
from fractions import Fraction
from functools import partial
import logging
import collections
from dataclasses import dataclass

import numpy as np
import sympy as sp

from pysmt.logics import QF_NRA, QF_LRA
from pysmt.typing import REAL
from pysmt.shortcuts import (
    get_env,
    Symbol, Real,
    Times, Minus, Plus,
    GE, LE, GT, LT, Equals,
    TRUE, FALSE,
    Not, And, Or, Implies, Iff,
    Exists,ForAll,
    qelim,
    get_model,
    is_valid,
    Solver,
)


import barrier.system as system

from barrier.formula_utils import (
    get_max_poly_degree, FormulaHelper
)

from barrier.lyapunov.lyapunov import synth_lyapunov_linear

from barrier.lyapunov.la_smt import (
    to_smt_vect, myround, to_sym_matrix, DEFAULT_PRECISION
)

from barrier.lyapunov.piecewise_quadratic import (
    _get_lyapunov_smt, PiecewiseQuadraticLF,
    validate_single_mode_smt
)


from barrier.lzz.lzz import (
    lzz, lzz_with_cex, LzzOpt, get_lzz_encoding,
    get_inf_dnf, get_ivinf_dnf
)

from barrier.utils import get_cvc5_smtlib, get_mathsat_smtlib

from barrier.mathematica.mathematica import (
    get_mathematica, exit_callback_print_time, OutOfTimeSolverError, MathematicaSession
)

from barrier.lyapunov.piecewise_quadratic_ludo import *

THETA = 1
PRECISION = 16
logging.basicConfig(level=logging.INFO)
stability_hs_logger = logging.getLogger(__name__)


GASOptions = collections.namedtuple(
    'GASOptions', ['use_linear', 'use_transpose', 'use_control', 'sdp_simple', 'sdp_exponential', 'read_from_file', 'write_on_file', 'validate_lyapunov', 'sdp_solver', 'alpha0', 'no_robust', 'use_determinant', 'validation_method']
)

# I do not know why we need this class.
class Config:
    """ Configurations for computing the assumptions """
    def __init__(self, solver_function):
        self.solver_function = solver_function



def handle_args():
    parser = argparse.ArgumentParser()

    parser = argparse.ArgumentParser()
    parser.add_argument("--problem",help="Verification problem file", default=None)

    parser.add_argument("--size",help="Pick standard verification problem file from valu3s", default=None)

    parser.add_argument("--abstraction",
                        choices=["factors","lie","invar","prop","preds_from_model"],
                        action='append', nargs='+',
                        help="Polynomials to use in the abstraction")

    parser.add_argument("--outvmt", help="Output vmt file")
    parser.add_argument("--outpred", help="Output predicates file")
    parser.add_argument("--solver",
                        choices=["z3","mathsat","cvc5","mathematica"],
                        default="mathematica",
                        help="SMT solver to use")
    
    parser.add_argument(
        '-o', '--output', dest='output', type=str, default="numeric_info.mat",
        help="Name of the output file"
    )

    # parser.add_argument(
    #     '-sp', '--sample-points', dest='sample_points', action='store_true'
    # )
    # parser.add_argument('--simulation-file', dest='simulation_file')

    parser.add_argument(
        '--input-num-info', dest='input_num_info', type=str,
        help="Name of the input matlab file where to find k0 and k1"
    )

    parser.add_argument('--use-linear', dest='use_linear', action='store_true')
    parser.add_argument('--use-transpose', dest='use_transpose', action='store_true')
    parser.add_argument('--use-control', dest='use_control', action='store_true')
    parser.add_argument('--use-exponential', dest='sdp_exponential', action='store_true')
    parser.add_argument('--use-simple', dest='sdp_simple', action='store_true')
    parser.add_argument('--no-determinant-opt', dest='use_determinant', action='store_false')
    parser.add_argument('--read-from-file0', dest='read_from_file0')
    parser.add_argument('--read-from-file1', dest='read_from_file1')
    parser.add_argument('--write-on-file0', dest='write_on_file0')
    parser.add_argument('--write-on-file1', dest='write_on_file1')

    parser.add_argument(
        '--validation-method', dest='validation_method',
        choices=['smt', 'sympy', 'sylvester'], default='smt'
    )
    
    # For exp eval: use non optimal values in get gas with --use-exponential
    parser.add_argument('--alpha0', dest='alpha0', action='store_true')
    parser.add_argument('--no-robust', dest='no_robust', action='store_true')
    parser.add_argument('--sdp-solver', dest='sdp_solver', default='cvxopt', choices=['cvxopt', 'mosek', 'smcp'])

    parser.add_argument(
        '--only', dest='only', type=int, choices=[0, 1],
        help='Find and validate lyapunov of this mode only. Allowed values are [0, 1].'
    )

    parser.add_argument('--skip-validation', dest='validate_lyapunov', action='store_false')
    parser.add_argument('--skip-synthesis', dest='synthesize', action='store_false')

    args = parser.parse_args()

    if args.problem == None and args.size == None:
        raise Exception("Must provide a problem. Enter the argument --size for standard ones.")

    if args.problem != None and args.size != None:
        raise Exception("Choose either one problem file or a size for a standard problem.")
    
    if args.size != None:
        args.problem = f"PI_controller_converter/Reformulate/hybrid_reformulation/reformulation_size_{args.size}.hyb"

    if args.input_num_info and not os.path.exists(args.input_num_info):
        raise Exception(f"File {args.input_num_info} does not exist.")

    if os.path.exists(args.output):
        logging.warning(f"Output file {args.output} already exists.")

    read_files = args.read_from_file0 is not None and args.read_from_file1 is not None
    if sum([args.read_from_file0 is not None, args.read_from_file1 is not None]) == 1:
        raise Exception("When reading Lyapunov from files, both files must be provided.")
    if sum([args.write_on_file0 is not None, args.write_on_file1 is not None]) == 1:
        raise Exception("When writing on files, both files must be provided.")
    for f in [args.read_from_file0, args.read_from_file1, args.write_on_file0, args.write_on_file1]:
        if f is not None and os.path.splitext(f)[1] not in [ '.npy', '.py']:
            raise Exception("All provided read/write files must be .npy or .py")
    for f in [args.read_from_file0, args.read_from_file1]:
        if f is not None and not os.path.exists(f):
            raise Exception(f"Provided file {f} does not exist.")
    if sum([args.use_transpose, args.use_linear, args.use_control, args.sdp_exponential, args.sdp_simple, read_files]) != 1:
        raise Exception("Must provide one and only option for GAS synthesis.")
    if not args.validate_lyapunov and not read_files:
        raise Exception("Cannot skip validation of a newly computed Lyapunov function. Use read_from_files options.")

    return args



def main(args):
    preds_from_model = False
    abs_type = AbsPredsTypes.NONE.value
    if args.abstraction:
        for l in args.abstraction:
            for t in l:
                if t == "factors":
                    abs_type = abs_type | AbsPredsTypes.FACTORS.value
                elif t == "prop":
                    abs_type = abs_type | AbsPredsTypes.PROP.value
                elif t == "lie":
                    abs_type = abs_type | AbsPredsTypes.LIE.value
                elif t == "invar":
                    abs_type = abs_type | AbsPredsTypes.INVAR.value
                elif t == "preds_from_model":
                    preds_from_model = True
                else:
                    raise Exception("Unknown abstraction type %s " % t)
    
    # Read HS
    print("Parsing problem...")
    env = get_env()
    with open(args.problem, "r") as f:
        problem = importHSVer(f, env)
    
    if (args.solver == "z3"):
        new_solver_f = partial(Solver, logic=QF_NRA, name="z3")
    elif (args.solver == "mathsat"):
        new_solver_f = partial(get_mathsat_smtlib)
    elif (args.solver == "cvc5"):
        new_solver_f = partial(get_cvc5_smtlib)
    elif (args.solver == "mathematica"):
        exit_callback_inst = partial(exit_callback_print_time, outstream=sys.stdout)
        new_solver_f = partial(get_mathematica,
                               budget_time=0,
                               env=get_env(),
                               exit_callback=exit_callback_inst)


    # Improve methods for more than 2 modes
    if len(problem.ha._locations) > 2:
        raise Exception("We are not ready to study stability of a Hybrid System with more than 2 modes.")
    
    # Here we check if the hybrid system given can be studied with valu3s tools.
    if not is_piecewise_affine(problem):
        raise Exception("We are not ready to study stability of this Hybrid System. At the moment we study\
                        stability for piecewise affine systems with two modes.")

    (dyn_systems, switching_predicate_mode0_less0, vector_sw_pr_mode0_less0) = build_dyn_systems_from_hs_file(problem)


    #LUDO: Todo: add a check on the stable points (both in mode 0)
    
    if args.validation_method in ['smt']:
        validate_during_synth = False
    else:
        validate_during_synth = True
    
    Candidate_lyap = get_piecewise_lyapunov_ludo(dyn_systems, vector_sw_pr_mode0_less0, certify = args.validation_method)
    if validate_during_synth == True:
        if Candidate_lyap == None:
            logging.critical("The synthesized Piecewise-Quadratic Lyapunov Function was NOT certified via symbolic methods. It is invalid.")
        else:
            Certified_Lyap = Candidate_lyap
            output_file_path = args.output
            logging.critical("Saving the Certified Lyapunov in %s..." % output_file_path)
            Certified_Lyap.serialize_mat(output_file_path)
            return Certified_Lyap
    
    else:
        certified = certify_piecewise_lyap(dyn_systems, switching_predicate_mode0_less0, Candidate_lyap, solver = new_solver_f())
        if certified == True:
            logging.critical("The Piecewise-Quadratic Lyapunov Function was certified via SMT methods. The system IS STABLE.")
            Certified_Lyap = Candidate_lyap
            output_file_path = args.output
            logging.critical("Saving the Certified Lyapunov in %s..." % output_file_path)
            Certified_Lyap.serialize_mat(output_file_path)
            if args.solver == "mathematica":
                MathematicaSession.terminate_session()
            return Certified_Lyap
        else:
            logging.critical("The synthesized Piecewise-Quadratic Lyapunov Function was NOT certified via SMT methods. It is invalid.")
    
    



    config = Config(new_solver_f)
    gas_optss = [
        # gas option for mode0
        GASOptions(
            use_linear=args.use_linear,
            use_transpose=args.use_transpose,
            use_control=args.use_control,
            sdp_simple=args.sdp_simple,
            sdp_exponential=args.sdp_exponential,
            use_determinant=args.use_determinant,
            read_from_file=args.read_from_file0,
            write_on_file=args.write_on_file0,
            validate_lyapunov=args.validate_lyapunov,
            sdp_solver=args.sdp_solver,
            no_robust=args.no_robust,
            alpha0=args.alpha0,
            validation_method=args.validation_method
        ),
        # gas option for mode1
        GASOptions(
            use_linear=args.use_linear,
            use_transpose=args.use_transpose,
            use_control=args.use_control,
            sdp_simple=args.sdp_simple,
            sdp_exponential=args.sdp_exponential,
            use_determinant=args.use_determinant,
            read_from_file=args.read_from_file1,
            write_on_file=args.write_on_file1,
            validate_lyapunov=args.validate_lyapunov,
            sdp_solver=args.sdp_solver,
            no_robust=args.no_robust,
            alpha0=args.alpha0,
            validation_method=args.validation_method
        )
    ]


    stability_hs_logger.info("Finding assumptions...")


    num_info = NumericInfo()
    output_file_path=args.output
    input_num_info_file=args.input_num_info
    synthesize=args.synthesize
    only=args.only
    try:
        stable, lyap = get_stable_and_lyapunov(dyn_systems, config.solver_function, gas_optss, num_info=num_info, only=only)

        if synthesize and only is None:

            assumptions, lyap = find_stability_assumption(config,
                                                          dyn_systems,
                                                          switching_predicate_mode0_less0,
                                                          stable, lyap,
                                                          num_info,
                                                          input_num_info_file)
            stability_hs_logger.info("Assumption computation completed...")

            stability_hs_logger.info("Found an assumption.") #, assumptions.serialize())

            # DEBUG
            solver = config.solver_function()
            if (not solver.is_sat(assumptions)):
                stability_hs_logger.info("WARNING: found inconsistent assumptions")
            else:
                stability_hs_logger.info("WARNING: assumptions ARE consistent!")
                if solver.is_sat(And(GT(switching_predicate_mode0_less0, Real(0)), assumptions)):
                    logging.critical(f"Assumptions intersects m1 invariant!")
                else:
                    logging.critical("Assumptions DO NOT intersects m1 invariant!")
        else:
            assumptions = None

    finally:
        if args.solver == "mathematica":
            MathematicaSession.terminate_session()

    stability_hs_logger.critical("Serializing the results in %s..." % output_file_path)
    num_info.serialize_mat(output_file_path)
    
    return assumptions

    
if __name__ == '__main__':
    args = handle_args()
    main(args)
    sys.exit(os.EX_OK)
