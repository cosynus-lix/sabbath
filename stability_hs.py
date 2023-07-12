""" Verify stability of a hybrid system
"""

import argparse
import logging
import os
import sys
from functools import partial

from pysmt.shortcuts import get_env

from barrier.decomposition.predicates import AbsPredsTypes
from barrier.stability.from_sabbath_to_matrices import (
    get_matrices_from_linear_odes,
    get_switching_predicate_from_linear_constraint,
    get_vector_from_linear_constraint)
from barrier.stability.piecewise_affine_case import *
from barrier.mathematica.mathematica import (MathematicaSession,
                                             exit_callback_print_time,
                                             get_mathematica)
from barrier.serialization.hybrid_serialization import importHSVer
# These are for the SMT solvers
from barrier.utils import get_cvc5_smtlib, get_mathsat_smtlib

try:
    from serialization import importSynthesis, serializeSynthesis
except:
    # Dirty trick to get around the current structure
    # and still have tests.
    from .serialization import serializeSynthesis, importSynthesis

import collections
import logging
import sys
from functools import partial

import numpy as np
import sympy as sp
from pysmt.logics import QF_NRA
from pysmt.shortcuts import *

import barrier.system as system
from barrier.lyapunov.la_smt import myround
from barrier.mathematica.mathematica import (MathematicaSession,
                                             exit_callback_print_time,
                                             get_mathematica)
from barrier.utils import get_cvc5_smtlib, get_mathsat_smtlib

PRECISION = 16
logging.basicConfig(level=logging.CRITICAL)
stability_hs_logger = logging.getLogger(__name__)


def handle_args():
    parser = argparse.ArgumentParser()

    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    parser.add_argument("--solver",
                        choices=["z3","mathsat","cvc5","mathematica"],
                        default="mathematica",
                        help="SMT solver to use")
    
    parser.add_argument(
        '-o', '--output', dest='output', type=str, default="numeric_info.mat",
        help="Name of the output file"
    )

    parser.add_argument('--use-linear', dest='use_linear', action='store_true')
    parser.add_argument('--use-transpose', dest='use_transpose', action='store_true')
    parser.add_argument('--use-control', dest='use_control', action='store_true')
    parser.add_argument('--use-exponential', dest='sdp_exponential', action='store_true')
    parser.add_argument('--use-simple', dest='sdp_simple', action='store_true')
    parser.add_argument('--no-determinant-opt', dest='use_determinant', action='store_false')

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

def build_dyn_systems_from_switched_ha(problem_ha, PRECISION = 16):
    Acs = []
    bs = []
    Cc = []
    
    for index_dyn_system in range(len(problem_ha._locations)):
        (A, b) = get_matrices_from_linear_odes(problem_ha._locations[f"{index_dyn_system}"][1])
        Acs.append(A)
        bs.append(b)
        (C, Theta) = get_vector_from_linear_constraint(problem_ha._locations[f"{index_dyn_system}"][0])
        Cc.append(C)
        if index_dyn_system == 0:
            Theta_smt = Theta
    
    dyn_systems = [system.DynSystem.get_dyn_sys_affine_description(Acs[0], bs[0]),
                   system.DynSystem.get_dyn_sys_affine_description(Acs[1], bs[1])]

    Theta_smt = Real(myround(Theta, PRECISION))

    # We get the switching predicate
    switching_predicate = get_switching_predicate_from_linear_constraint(problem_ha._locations["0"][0])

    return (dyn_systems, switching_predicate, Theta_smt) # ,ref_values_smt)

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
    if not problem.ha.is_piecewise_affine:
        raise Exception("We are not ready to study stability of this Hybrid System. At the moment we study\
                        stability for piecewise affine systems with two modes.")

    (dyn_systems, switching_predicate, Theta_smt) = build_dyn_systems_from_switched_ha(problem.ha)
    
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
                                                          switching_predicate,
                                                          stable, lyap,
                                                          num_info,
                                                          input_num_info_file)
            stability_hs_logger.info("Assumption computation completed...")

            stability_hs_logger.info("Found an assumption.") #, assumptions.serialize())

        else:
            assumptions = None

    finally:
        if args.solver == "mathematica":
            MathematicaSession.terminate_session()

    stability_hs_logger.info("Serializing the results in %s..." % output_file_path)
    num_info.serialize_mat(output_file_path)
    
    return assumptions

    
if __name__ == '__main__':
    args = handle_args()
    main(args)
    sys.exit(os.EX_OK)
