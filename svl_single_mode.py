import logging
import numpy as np
from scipy import linalg
import picos as pc
import control

from barrier.lyapunov.piecewise_quadratic import (
    Affine, LeConst, Edge, NumericAffineHS, PiecewiseQuadraticLF,
    get_ge,
    validate, validate_single_mode
)

def global_asymptotic_stability_numpy(Ac, gas_opts):
    """
    Synthesise a lyapunov function proving global asymptitic stability
    for the linear homogeneus system der(x) = Ax + b.

    The input is NumPy matrix.

    Return the matrix P such that the lyapunov function is V(x) = x^T P x
    """

    if gas_opts.read_from_file:
        import os
        from numpy import array
        logging.critical(f'Reading from file {gas_opts.read_from_file}')
        if os.path.splitext(gas_opts.read_from_file)[1] == '.npy':
            P = np.load(gas_opts.read_from_file)
        else:
            with open(gas_opts.read_from_file, 'r') as fin:
                str_P = fin.read()
            P = eval(str_P)
        return P

    if gas_opts.use_transpose:
        logging.critical(f'Synthesizing lyapunov with transpose')
        evAc, vAc = np.linalg.eig(Ac)
        vAcinv = np.linalg.inv(vAc)
        P = np.real(np.dot(np.conj(np.transpose(vAcinv)),vAcinv))
        return P

    if gas_opts.use_control:
        logging.critical(f'Synthesizing lyapunov with control')
        Q = np.identity(len(Ac))
        P = control.lyap(np.transpose(Ac), Q)
        return P

    # here is use SDP
    if gas_opts.sdp_exponential:
        logging.critical(f'Synthesizing lyapunov with exponential')
        n = len(Ac)

        if gas_opts.alpha0:
            alphac = 0.1
        else:
            # compute alpha
            alphac = round(2 * min( abs(np.real(x)) for x in np.linalg.eig(Ac)[0] ) - 0.01, 2)
        logging.critical(f'Found alpha = {alphac}')
        
        solver_name = gas_opts.sdp_solver
        logging.critical(f'Solving with {solver_name}')
        
        candidate_best = None
        delta_robustness = 0.0000000001
        while delta_robustness < 1: # CHECK: is there an upper bound?
            try:
                sdp = pc.Problem()
                alpha = pc.Constant("alpha", alphac)
                P = pc.SymmetricVariable("P", n)
                if not gas_opts.no_robust:
                    nu = pc.RealVariable("nu")
                    sdp.add_constraint(nu >> delta_robustness)
                    I = pc.Constant("I", np.identity(n))
                    sdp.add_constraint(P - nu * I >> 0)
                else:
                    sdp.add_constraint(P >> 0)
                A = pc.Constant("A", Ac)
                # sdp.add_constraint(A.T * P + P * A + alpha * P + nu * I << 0)
                sdp.add_constraint(A.T * P + P * A + alpha * P << 0)
                sol = sdp.solve(solver=solver_name)

                candidate_best = P.np

                logging.info("Try to increase nu")
                delta_robustness *= 10

            except pc.modeling.problem.SolutionFailure:
                break

        if candidate_best is None:
            raise pc.modeling.problem.SolutionFailure()

        logging.info(f"Found with nu = {delta_robustness / 10}")
        return candidate_best

    if gas_opts.sdp_simple:
        logging.critical(f'Synthesizing lyapunov with simple')
        solver_name = gas_opts.sdp_solver
        logging.critical(f'Solving with {solver_name}')

        sdp = pc.Problem()
        P = pc.SymmetricVariable("P", len(Ac))
        sdp.add_constraint(P >> 0)
        A = pc.Constant("A", Ac)
        sdp.add_constraint(A.T * P + P * A << 0)

        # TODO: what if there is no solution? (not handled now)
        sol = sdp.solve(solver=solver_name)
        Xnum = P.np

        return P.np

    raise Exception("No option was chosen for synthesizing lyapunov function.")

# Note: This code is extracted from routine used in `svl_ohlerking1` and modified to use only one modality.
def create_HS(Ac, b, C, Theta, mode1=True):
    n = len(Ac)

    # single modality
    modes = set([1])

    # CHECKME.
    # Note: in the svl_ohlerking1 etc approaches, `b` is `np.zeros()`,
    # since they work with the translated matrix.
    # Here, it should use the original b matrix.
    flow = { 1 : [Affine(Ac, b)] }

    edges = []

    # CHECKME: is this the right implementation of the invariant y0 - r0 > theta ?
    # recall: refs values should have been embedded as values in the A matrix.
    v = np.zeros(n)
    v[0] = - Theta
    M = np.vstack([
        C[0],
        np.zeros([n-1, n])
    ])
    if mode1:
        # y0 - r0 > theta
        m1_invar = [get_ge(M, v)]
    else:
        m1_invar = [LeConst(M, v)]
    invariant = { 1 : m1_invar }

    hs = NumericAffineHS(modes, n, flow, edges, invariant, True)
    hs.has_last_var_dummy = True

    return hs

def svl_single_mode(Ac, b, C, Theta, mode1=False, verbose=False):
    n = len(Ac)

    # Create a Numeric Affine HS
    hs = create_HS(Ac, b, C, Theta, mode1)

    hs.make_homogeneous()


    # Create a Lyapunov function
    lf =  PiecewiseQuadraticLF()
    # TODO: CHECK THESE PARAMETERS.
    # these are common to every strategy.
    lf.alpha, lf.beta, lf.gamma = (0, 0.1, 0)

    Ibar = np.vstack([
        np.hstack([np.identity(n-1), np.zeros([n-1,1])]),
        np.zeros([1,n])
    ])
    lf.I_tilda = { 1 : Ibar }

    # Helpers: 3 different approaches to synthesize Lyapunov func.

    # approach 1: simple stability
    # expose simple stability
    def simple_stability():
        return global_asymptotic_stability_numpy(Ac)

    # approach 2: exponential stability: Note: cannot be validated right now.
    def exponential_stability(alphac):
        sdp = pc.Problem()
        P = pc.SymmetricVariable("P", n)
        sdp.add_constraint(P >> 0)
        A = pc.Constant("A", Ac)
        alpha = pc.Constant("alpha", alphac)
        sdp.add_constraint(A.T * P + P * A + alpha * P << 0)
        sol = sdp.solve()

        return P.np

    # approach 3: can be validated
    def exponential_stability_with_robustness_variable(alphac, delta_robustness=0.0001):
        sdp = pc.Problem()
        alpha = pc.Constant("alpha", alphac)
        P = pc.SymmetricVariable("P", n)
        nu = pc.RealVariable("nu")

        sdp.add_constraint(nu >> delta_robustness)

        I = pc.Constant("I", np.identity(n))
        sdp.add_constraint(P - nu * I >> 0)
        A = pc.Constant("A", Ac)

#        sdp.add_constraint(A.T * P + P * A + alpha * P << 0)
        sdp.add_constraint(A.T * P + P * A + alpha * P + nu * I << 0)

        sol = sdp.solve()
        # TODO CHECK SOLUTION

        return P.np
    #eof helpers

    # TODO: add dispatcher between the three approaches.

    print("Synthesising a Lyapunov function...")

    pick = 0
    if (pick == 0):
        Pnp = simple_stability()
        lf.lyapunov_map = { 1 : Pnp }
        val_fun = lambda : validate_single_mode(hs, lf, 1)
    elif (pick == 1):
        alpha = 3.43 # Alberto: 3.44 has eigenvalues ~ 10^-14
        Pnp = exponential_stability(alpha)
        lf.lyapunov_map = { 1 : Pnp }
        val_fun = lambda : validate_single_mode(hs, lf, 1, True, alpha)
    elif (pick == 2):
        alpha = 3.43
        robustness = 0.00000001
        robustness = 0.0000001
        Pnp = exponential_stability_with_robustness_variable(alpha, robustness)
        lf.lyapunov_map = { 1 : Pnp }
        val_fun = lambda : validate_single_mode(hs, lf, 1, True, alpha)
    else:
        raise Exception()

    print("Validating the function...")
    (is_valid, lyapunov_function_smt) = val_fun()

    print (f"synthetized Lyapunov")
    if is_valid:
#    if validate(hs, lf):
        print ("OK: validation of Lyapunov function")
        return (is_valid, lyapunov_function_smt[1])
    else:
        print ("FAIL: validation of Lyapunov function")
        return (is_valid, None)
