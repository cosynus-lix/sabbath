"""
This module contains the main functions to study piecewise affine dynamical systems.
The main entry points are get_gas_lyapunov and find_stability_assumption.
"""

import functools
import logging
import os
import time
from enum import Enum

from pysmt.shortcuts import get_env

from barrier.stability.piecewise_affine_case import *

try:
    import reformulate
    import svl_single_mode
except:
    # Dirty trick to get around the current structure
    # and still have tests.
    from . import reformulate
    from . import svl_single_mode

import logging
from fractions import Fraction

import numpy as np
import sympy as sp
from pysmt.shortcuts import *
from pysmt.typing import REAL

import barrier.system as system
from barrier.formula_utils import FormulaHelper, get_max_poly_degree
from barrier.lyapunov.la_smt import (myround, to_smt_vect,
                                     to_sym_matrix)
from barrier.lyapunov.lyapunov import synth_lyapunov_linear
from barrier.lyapunov.piecewise_quadratic import (PiecewiseQuadraticLF,
                                                  _get_lyapunov_smt,
                                                  validate_single_mode_smt)
import collections

logging.basicConfig(level=logging.CRITICAL)
stability_hs_logger = logging.getLogger(__name__)

GASOptions = collections.namedtuple(
    'GASOptions', ['use_linear', 'use_transpose', 'use_control', 'sdp_simple', 'sdp_exponential', 'read_from_file', 'write_on_file', 'validate_lyapunov', 'sdp_solver', 'alpha0', 'no_robust', 'use_determinant', 'validation_method']
)

class Config:
    """ Configurations for computing the assumptions """
    def __init__(self, solver_function):
        self.solver_function = solver_function

class Result(Enum):
    STABLE = True
    UNSTABLE = False
    UNKNOWN = True + 1


class NumericInfo:
    def __init__(self):
        self.As = [None, None]
        self.bs = [None, None]
        self.switching_pred = None
        self.stables = [None, None]
        self.homo_lyap = [None, None]
        self.ks = [None, None]
        self.crosses = [None, None]
        self.lies = [None, None]
    def serialize_mat(self, filename):
        from scipy.io import savemat
        data = {
            "A0" : self.As[0],
            "A1" : self.As[1],
            "B0" : self.bs[0],
            "B1" : self.bs[1],
            "switching_pred" : self.switching_pred,
            "stable0" : self.stables[0],
            "stable1" : self.stables[1],
            "homo_lyap0" : self.homo_lyap[0],
            "homo_lyap1" : self.homo_lyap[1],
        }
        none_keys = [ v for v in data if data[v] is None]
        for v in none_keys:
            del data[v]

        if self.ks[0] is not None:
            data.update({
                "k0" : self.ks[0],
                "k1" : self.ks[1],
                "crosses0" : 1 if self.crosses[0] else 0,
                "crosses1" : 1 if self.crosses[1] else 0,
                "lies0" : self.lies[0],
                "lies1" : self.lies[1],
            })
        savemat(filename, data)

def get_y0(dyn_sys, C, PRECISION=16):
    """
    Get only the first output y0. The outputs Y = C x.
    """
    y0 = Real(0)
    for j in range(len(C[0])):
        y0 = y0 + Times(Real(myround(C[0][j], PRECISION)), dyn_sys._states[j])
    return y0

def validate_single_mode_sympy(P_sym, A_sympy):
    s = time.time()
    logging.info("validating V(x) > 0 for all x != 0")
    positive = P_sym.is_positive_definite
    if not positive:
      logging.critical("C1 is invalid: V(x) <= 0 for some x != 0")
      return False
    s1 = time.time()
    logging.critical(f"Time for validating c1: {round(s1 - s, 2)}")

    logging.info("validating der(V)(x) < 0 for all x != 0")
    s = s1
    Matrix_V_m_der = (sp.transpose(A_sympy) @ P_sym) + (P_sym @ A_sympy)
    negative = Matrix_V_m_der.is_negative_definite
    if not negative:
      logging.critical("C2 is invalid: der(V)(x) >= 0 for some x != 0")
      return False
    s1 = time.time()
    logging.critical(f"Time for validating c2: {round(s1 - s, 2)}")
    return True

def is_positive_sylvester(A):
  # Note: could be optimized
  n = sp.shape(A)[0]
  for i in range(n-1):
    if sp.Determinant(A).doit() <= 0:
      return False
    A = A.minor_submatrix(0, 0)
  return sp.Determinant(A).doit() > 0

def validate_single_mode_sylvester(P_sym, A_sympy):
    s = time.time()
    logging.info("validating V(x) > 0 for all x != 0")
    positive = is_positive_sylvester(P_sym)
    if not positive:
      logging.critical("C1 is invalid: V(x) <= 0 for some x != 0")
      return False
    s1 = time.time()
    logging.critical(f"Time for validating c1: {round(s1 - s, 2)}")

    logging.info("validating der(V)(x) < 0 for all x != 0")
    s = s1
    Matrix_V_m_der = (sp.transpose(A_sympy) @ P_sym) + (P_sym @ A_sympy)
    negative = is_positive_sylvester(- Matrix_V_m_der)
    if not negative:
      logging.critical("C2 is invalid: der(V)(x) >= 0 for some x != 0")
      return False
    s1 = time.time()
    logging.critical(f"Time for validating c2: {round(s1 - s, 2)}")
    return True


def get_gas_lyapunov(dyn_sys, solver_function, gas_opts, num_info=None, mode=None):
    """
    Wrap the computation of an global asymptotic stable lyapunov
    function for dyn_sys.

    Assume dyn_sys is homogeneous and stable point is in 0.

    To be moved in the tool...

    Return the lyapunov function, if found, or None.
    """

    # Compute the lyapunov function with numeric methods

    s = time.time()
    # Note: minus_b has to be 0, we expect dyn_sys to be homogeneous
    A_sympy, minus_b = dyn_sys.get_derivator().get_sympy_matrix_equations(dyn_sys._odes.values(),
                                                                          dyn_sys.states())
    
    A0 = np.array(A_sympy).astype(np.float64)
    try:
        stability_hs_logger.info("Searching a lyapunov function candidate...")
        Pnp = svl_single_mode.global_asymptotic_stability_numpy(
            A0,
            gas_opts
            )
    except Exception as e:
        raise e
        stability_hs_logger.info("Error searching for the Lyapunov function")
        return None
    s1 = time.time()
    logging.critical(f"Time for synthesizing lyapunov: {round(s1 - s, 2)}")

    if gas_opts.write_on_file:
        if os.path.splitext(gas_opts.write_on_file)[1] == '.npy':
            np.save(gas_opts.write_on_file, Pnp)
        else:
            with open(gas_opts.write_on_file, 'w') as fout:
                fout.write(repr(Pnp))

    if num_info:
        num_info.homo_lyap[mode] = Pnp

    # Convert lyapunov to SMT
    lf = PiecewiseQuadraticLF( )
    lf.lyapunov_map = { 0 : Pnp }
    lf.alpha = 0
    lf.beta = 0
    lf.gamma = 0
    lf.edge_slack = 0

    lyapunov_smt = {}
    smt_vars = [v for v in dyn_sys.states()]
    P_sym = to_sym_matrix(Pnp)
    V_m_list = _get_lyapunov_smt(smt_vars, lf, lyapunov_smt, 0)
    assert(len(V_m_list) == 1)
    for el in V_m_list:
        # V_m is the lyapunov function
        (condition, V_m) = el
        break

    if not gas_opts.validate_lyapunov:
        assert gas_opts.read_from_file
        stability_hs_logger.warning("Skipping validation of a read Lyapunov function...")
        return V_m

    # Validate the lyapunov function
    stability_hs_logger.info("Validating the Lyapunov function...")

    s = time.time()

    if gas_opts.validation_method == 'smt':
        (res, _) = validate_single_mode_smt(dyn_sys.get_derivator(),
                                            smt_vars,
                                            TRUE(), # should hold for all the domain
                                            V_m, P_sym, A_sympy, 0,
                                            False, #gas_opts.sdp_exponential,
                                            Real(0), #compute alpha
                                            solver_function(),
                                            use_determinant=gas_opts.use_determinant)
    elif gas_opts.validation_method == 'sympy':
        res = validate_single_mode_sympy(P_sym, A_sympy)
    else:
        assert gas_opts.validation_method == 'sylvester'
        res = validate_single_mode_sylvester(P_sym, A_sympy)
    
    s1 = time.time()
    logging.critical(f"Time for validating lyapunov: {round(s1 - s, 2)}")
    if res:
        return V_m
    else:
        stability_hs_logger.info("The lyapunov function is not valid (SMT check failed)")
        return None

def compute_lyapunov(dyn_sys, solver_function, gas_opts, num_info=None, mode=None):
    """ Compute the stable points and the lyapunov function

    Return a triple (is_stable, equilibrium_point, lyapunov_function)

    """
    stable = None
    lyap = None
    stable_systems = dyn_sys.get_rescaled_by_equilibrium_point()
    if (stable_systems is None):
        stability_hs_logger.info("Cannot find a stability point (or single point) found")
        return (False, None, None)
    elif len(stable_systems) > 1:
        stability_hs_logger.info("Find multiple stable_systems points, ignore the system")
        return (False, None, None)
    else:
        stable = stable_systems[0]
        homogeneous_sys = stable[0]
        if not gas_opts.use_linear:
            lyap = get_gas_lyapunov(homogeneous_sys, solver_function, gas_opts, num_info, mode)
        else:
            s = time.time()
            logging.critical("Synthesizing the lyapunov function with linear")
            (res, lyap) = synth_lyapunov_linear(homogeneous_sys, solver_function())
            s1 = time.time()
            logging.critical(f"Time for synthesizing lyapunov: {round(s1 - s, 2)}")

        if lyap is None:
            stability_hs_logger.info("Cannot find lyapunov")
            return (False, None, None)
        else:
            # Change back to the original coordinate system
            lyap_for_dyn_sys = lyap.substitute(stable[2])

            # # DEBUG
            # print(",".join([str(l) for l in  dyn_sys.states()]))
            # print(lyap.serialize())
            # print(lyap_for_dyn_sys.serialize())

            return (True, stable[1], lyap_for_dyn_sys)


def find_inward_region(dyn_system, switching_predicate, use_le_for_lie = False):
    """
    Returns the subset of switching_predicate that is guarnateed
    to stay inside switching_predicate < 0.

    We compute an under-approximation of the inward_region, taking
    the subset of switching_predicate such that the first Lie
    derivative is negative (one could do better in case Lie
    derivatives have vanishing points, i.e., points where the Lie
    derivative is 0).
    """
    derivator = dyn_system.get_derivator()
    lie_switching_predicate = derivator.get_lie_der(switching_predicate)

    # ensure lie_switching_predicate is linear
    assert(get_max_poly_degree(lie_switching_predicate) <= 1)

    op = LE if use_le_for_lie else LT
    return And(Equals(switching_predicate, Real(0)),
               op(lie_switching_predicate, Real(0)))

@functools.lru_cache(maxsize=10)
def find_level_set(config, lyap, switching_surface, beta,
                   delta = Fraction(1,100),
                   init_lower = None,
                   init_upper = None,
                   num_info=None, mode=None,
                   k_init = None):
    # Synthesise the (maximum) natural number k such that:
    # (lyap <= k & switching_surface) -> beta
    # and returns either:
    # - lyap <= k, if k max
    # - TRUE if lyap <= k for all k
    #
    # Note: the condition above holds for k = 0.
    solver = config.solver_function()
    solver2 = config.solver_function()

    k = FormulaHelper.get_fresh_var_name(get_env().formula_manager,
                                         "K",
                                         REAL)

    assert (init_lower == init_upper or (init_lower != None and init_upper != None and init_lower <= init_upper))

    has_init_bound = init_lower != None and init_upper != None

    cond = Implies(And(GE(k,Real(0)), LE(lyap, k), switching_surface), beta)

    if k_init is not None:
        k_init_smt = Real(myround(k_init * 0.999))
        cond_k = cond.substitute({k : k_init_smt})
        if solver.is_valid(cond_k):
            stability_hs_logger.info("Validated numeric K * 0.999.")

            k_init_smt_gt = Real(myround(k_init * 1.001))
            cond_k = cond.substitute({k : k_init_smt_gt})
            if solver.is_valid(cond_k):
                stability_hs_logger.warning("Numeric K is NOT close to the optimal value.")
            else:
                stability_hs_logger.info("Numeric K is close to the optimal value.")

            if num_info:
                num_info.ks[mode] = k_init * 0.999
            return LE(lyap, k_init_smt)
        else:
            stability_hs_logger.info("Invalid numeric K!! Going back to binary search.")

    # Check if (lyap <= k & switching_surface) -> beta for all k
    if not has_init_bound:
        stability_hs_logger.info("Checking for validity")
        is_valid = solver.is_valid(cond)
    else:
        stability_hs_logger.warning("Using user-provided initial lower/upper bounds")
        assert solver.is_valid(cond.substitute({k : init_lower}))
        is_valid = True

    if (not has_init_bound and is_valid):
        # # solution is vacuous if switching_surface does not contain the equilibrium point
        # is_vacuous = not solver.is_sat(And(LE(lyap, k), switching_surface))
        # print("No upper bound, is it vacuous? ", is_vacuous)

        stability_hs_logger.warning("Conditions are valid for all k...")
        if num_info:
            num_info.ks[mode] = True
 
        return TRUE()
    elif (has_init_bound or not is_valid):
        # Found a k such that cond does not hold.
        # If a k' exists it must be lower than k. We find it by a bisection search.
        stability_hs_logger.info("Found a valid k...")

        # We find a k' such that |greatest - k'| <= delta


        if (not has_init_bound):
            lower_bound = Real(0) # cond holds on lower bound
            upper_bound = solver.get_value(k) # cond does NOT hold on upper bound
        else:
            lower_bound = init_lower
            upper_bound = init_upper

        middle = FormulaHelper.get_fresh_var_name(get_env().formula_manager,
                                                  "middle",
                                                  REAL)
        delta_smt = Real(delta)

        solver2.is_sat(TRUE()) # hack to evaluate the results
        while (TRUE() == solver2.get_value(GT(upper_bound - lower_bound, delta_smt))):
            middle_val = solver2.get_value( lower_bound + Real(0.5) * (upper_bound - lower_bound))

            # cond and k >= (upper - lower)
            new_cond = cond.substitute({k : middle_val})

            # Avoid SMT2-lib issue with cvc5
            solver = config.solver_function()
            if solver.is_valid(new_cond):
                # print("Valid!")
                lower_bound = middle_val
            else:
                # print("Not valid!")
                upper_bound = middle_val

            stability_hs_logger.info("Delta,lower,upper: %.2f,%.2f,%.2f" % (
                float(Fraction(solver2.get_value(upper_bound - lower_bound).serialize())),
                float(Fraction(lower_bound.serialize())),
                float(Fraction(upper_bound.serialize()))))

        # lower_bound at the loop exit approximates the greatest value
        stability_hs_logger.info("FOUND APPROX UPPER BOUND %f" % float(Fraction(lower_bound.serialize())))

        if num_info:
            num_info.ks[mode] = float(Fraction(lower_bound.serialize()))

        return LE(lyap, lower_bound)
    else:
        stability_hs_logger.warning("No suitable K found!")
        if num_info:
            num_info.ks[mode] = False
        return FALSE()

def get_stable_and_lyapunov(dyn_systems, get_solver, gas_optss, num_info=None, only=None):
    """
    Get stability and lyapunov conditions for the systems
    """
    # 1 - stable points and lyapunov functions
    stable = [None for i in dyn_systems]
    lyap = [None for i in dyn_systems]
    for i in range(len(dyn_systems)):
        if only is not None and i != only:
            continue
        all_stable, stable[i], lyap[i] = compute_lyapunov(
            dyn_systems[i],
            get_solver,
            gas_opts=gas_optss[i],
            num_info=num_info,
            mode=i
        )

        if not all_stable:
            stability_hs_logger.info("A mode is not stable!")
            # cannot stabilize the mode in isolation
            raise Exception("cannot prove stability of modes.")
    stability_hs_logger.info("All modes are stable")

    return (stable, lyap)

def set_dyn_system_numeric_info(num_info, Acs, bs, Cc, refs, ctl, mod, THETA = 1):
    num_info.stables = [np.linalg.solve(Acs[i], -bs[i]) for i in range(len(Acs))]
    num_info.switching_pred = np.hstack([-Cc[0], - THETA + refs[0]])
    num_info.As = Acs
    n = mod.dimension()
    num_info.bs = [np.vstack([np.zeros([n,len(refs)]), ctl.KI[mode]]) for mode in range(ctl.modes)]

def build_dyn_systems(mod, ctl, refs, new_solver_f, num_info=None, THETA = 1, PRECISION=16):
    (Acs, bs, bprimes, Cc) = reformulate.reformulate(mod, ctl, refs)

    if num_info:
        set_dyn_system_numeric_info(num_info, Acs, bs, Cc, refs, ctl, mod)

    dyn_systems = [system.DynSystem.get_dyn_sys_affine_description(Acs[0], bs[0]),
                   system.DynSystem.get_dyn_sys_affine_description(Acs[1], bs[1])]
    
    Theta_smt = Real(myround(THETA, PRECISION))
    y0 = get_y0(dyn_systems[0], Cc)
    refvalues_smt = to_smt_vect(refs, PRECISION)

    stability_hs_logger.info("Reference values: %s" % str(refvalues_smt))

    r0 = refvalues_smt[0]

    # r0 - y0 - Theta
    switching_predicate = r0 - y0 - Theta_smt

    config = Config(new_solver_f)

    return (config, dyn_systems, switching_predicate, Theta_smt, refvalues_smt)


def minimize_k(config, formula, f, k):
    """
    Find a minimum k such that: Exists k. forall X. formula(X) -> f(X) < k

    The function finds a minumum up to delta.
    """

    stability_hs_logger.debug("Minimizing...")

    solver = config.solver_function()
    k_val = Real(0)
    delta = Real(Fraction(1,1000))
    f_bound = And(formula, GE(k, k_val))
    while (solver.is_sat(And(f_bound, GE(f,k)))):
        k_val = solver.get_value(f + delta)
        stability_hs_logger.debug("Found cex %.2f" % float(Fraction(k_val.serialize())))

        # Cex, remove from next search
        f_bound = And(formula, GE(k, k_val))

    stability_hs_logger.debug("Found k close enough %.2f" % float(Fraction(k_val.serialize())))
    return True, k_val

def verify_stability_aux(config, dyn_systems, stable, lyap, switching_predicate, x):
    """
    Check if a state of the switched system is stable (i.e., it stabilizes
    to a stable point).

    There are a total of 8 cases, considering if the stability points of each
    mode are in the mode or not, and if the point x is in a mode or the other.
    By symmetry, we have only 4 cases in total to consider.

    """

    # Deciding the case we are in:
    solver = config.solver_function()

    switching_surface = Equals(switching_predicate, Real(0))
    m0_invar = LE(switching_predicate, Real(0))
    m1_invar = GT(switching_predicate, Real(0))
    s0_in_m0 = solver.is_sat(m0_invar.substitute(stable[0]))
    s1_in_m0 = solver.is_sat(m0_invar.substitute(stable[1]))
    x_in_m0 = solver.is_sat(m0_invar.substitute(x))

    swapped = False
    if (not x_in_m0):
        # If x is not in m0 we swap the two modes, so we reduce checking
        # the 8 cases to checking 4.
        # After this we assume x to be in the mode m0 (which is m1...)
        stability_hs_logger.info("Swapping m0 with m1.")
        dyn_systems = [dyn_systems[1], dyn_systems[0]]
        lyap = [lyap[1],lyap[0]]
        m0_invar,m1_invar = m1_invar, m0_invar
        s0_in_m0,s1_in_m0 = (not s0_in_m0, not s1_in_m0)

        switching_predicate = Minus(Real(0),switching_predicate)
        switching_surface = Equals(switching_predicate, Real(0))

        x_in_m0 = True
        swapped = True

    # Compute the minimum level set containing x
    k0 = FormulaHelper.get_fresh_var_name(get_env().formula_manager, "K0", REAL)
    k1 = FormulaHelper.get_fresh_var_name(get_env().formula_manager, "K1", REAL)
    res = solver.is_sat(Equals(lyap[0].substitute(x), k0))
    assert res # there must be a k0 that intersect x (lyap is an ellipsoid)
    k0_val = solver.get_value(k0)
    stability_hs_logger.info("Found k0 = %.10f" % float(Fraction((k0_val.serialize()))))

    f0_le_k0 = LE(lyap[0], k0_val)
    f1 = lyap[1]
    sw_der_m0 = dyn_systems[0].get_derivator().get_lie_der(switching_predicate)
    sw_der_m1 = dyn_systems[1].get_derivator().get_lie_der(switching_predicate)

    is_stable_in_m0 = False
    if (s0_in_m0):
        # Common case where the boundary with m0 is a differential invariant
        stability_hs_logger.info("Checking if boundary with m0 is a differential invariant. (i.e. point does not cross switching surface)")
        stays_in_m0 = Implies(And(f0_le_k0, switching_surface), LT(sw_der_m0, Real(0)))
        if (solver.is_valid(stays_in_m0)):
            stability_hs_logger.info("The point is stable")
            return Result.STABLE
        else:
            stability_hs_logger.info("The point may cross the switching surface and may not be stable")

    if (s0_in_m0 and s1_in_m0):
        # Both equilibrium points are in m0, we prove that x stays in m0
        stability_hs_logger.info("CASE A: m0 already in the mode containing the stable point.")

        # TODO: Implement check comparing values of the Lyapunov functions
        return Result.UNKNOWN

    elif ((s0_in_m0 and not s1_in_m0) or (not s0_in_m0 and not s1_in_m0)):
        # Now we check the same sufficient condition for both cases
        if (s0_in_m0 and not s1_in_m0):
            stability_hs_logger.info("CASE B: ss0 in m0 and ss1 in m1")
        else:
            stability_hs_logger.info("CASE C: ss0 in m1 and ss1 in m1")

        # May enter in m1 from m0
        may_enter_m1 = And(f0_le_k0, switching_surface, GE(sw_der_m0, Real(0)))

        # Find the minimum level set that contains the switching surface
        res, min_val = minimize_k(config, may_enter_m1, f1, k1)

        if res:
            # Prove that the level set is in M1
            f1_le_k1 = LE(lyap[1], min_val)
            stays_in_m1 = And(f1_le_k1, switching_surface, GT(sw_der_m1, Real(0)))
            if (solver.is_valid(Implies(may_enter_m1, stays_in_m1))):
                stability_hs_logger.info("The point is stable")
                return Result.STABLE
            else:
                # print(solver.get_value(f1_le_k1))
                # print(solver.get_value(GE(sw_der_m1, Real(0))))

                stability_hs_logger.info("The boundary of the level set of m1 and switch is not a differential invariant")
                return Result.UNKNOWN
        else:
            stability_hs_logger.info("Did not find any suitable K1!")
            return Result.UNKNOWN

    elif (not s0_in_m0 and s1_in_m0):
        # Cannot be stable (m0 stabilizes in m1 and m1 stabilizes in m0).
        stability_hs_logger.info("The point cannot be stable!")
        return Result.UNSTABLE

    else:
        # Should not happen.
        raise Exception("Unknown case!")



def verify_stability_dyn_system(config, dyn_systems, switching_predicate, x, gas_optss):
    """
    Check that a state of the switched system is stable
    """

    # To move out
    res = get_stable_and_lyapunov(dyn_systems, config.solver_function, gas_optss)
    if res is None:
        return False
    stable,lyap = res

    return verify_stability_aux(config, dyn_systems,
                                stable, lyap,
                                switching_predicate, x)



def sample_stability_aux(config, dyn_systems, switching_predicate, gas_optss, simul_file):
    """
    Check that a state of the switched system is stable
    """

    verified = False
    res = get_stable_and_lyapunov(dyn_systems, config.solver_function, gas_optss)
    if res is None:
        return False
    stable,lyap = res

    smt_vars = [v for v in dyn_systems[0].states()]
    n = len(smt_vars)
    assert verify_stability_aux(
        config, dyn_systems,
        stable, lyap,
        switching_predicate, stable[0]
    )

    # Helper data structures to uniform different sampling strategies.
    class Point:
        def __init__(self, x):
            self.x = x
        def __eq__(self, y):
            return self.x == y
        def get(self):
            return self.x
        def str_point(self):
            return ",".join(str(round(float(Fraction(self.x[v].serialize())),10)) for v in self.x)
    class GridPoint(Point):
        def __init__(self, x, deltas):
            super().__init__(x)
            self.deltas = deltas.copy()
        def __str__(self):
            return f"Deltas from stable point: {self.deltas}"
    class SimulationPoint(Point):
        def __init__(self, x, t):
            super().__init__(x)
            self.t = t
        def __str__(self):
            return f"Time step: {self.t}"

    def generate_points_from_grid(max_abs_val, step):
        '''
        Generate points around the m0 stable point in a grid, by trying
        every configuration in the box [m0 - max_abs_val, m0 + max_abs_val]
        '''
        points = []
        m0_stable_val = [ stable[0][x].simplify() for x in smt_vars ]
        # "deltas" is how much the current value differs from the stable point
        # Note: lb/ub boudaries could be set differently for each variable.
        # Here try by varying only the first variable (x0) and keeping the others at the stable point.
        lb_deltas = [ -max_abs_val if i == 0 else 0 for i in range(n) ]
        ub_deltas = [ max_abs_val if i == 0 else 0 for i in range(n) ]
        # initialize from the lower distance
        x_deltas = lb_deltas.copy()
        while True:
            print('add')
            for i in range(n):
                if x_deltas[i] + step <= ub_deltas[i]:
                    x_deltas[i] += step
                    break
                else:
                    x_deltas[i] = lb_deltas[i]
            x = {
                v : Plus(m0_stable_val[i], Real(x_deltas[i])).simplify()
                for i, v in enumerate(smt_vars)
            }
            point = GridPoint(x, deltas=x_deltas)
            assert point not in points
            points.append(point)
            # check if x == lbs again.
            if all(x_deltas[i] == lb_deltas[i] for i in range(n)):
                break
        return points

    def generate_points_from_simulation(simul_file):
        stability_hs_logger.info(f"Extracting points from simulation: {simul_file}")
        points = []
        import scipy.io
        mat = scipy.io.loadmat(simul_file)
        xs = np.array(mat['xdata'], dtype='float')
        xn = len(xs[0])
        us = np.array(mat['udata'], dtype='float')
        time_horizon = len(us)
        assert len(us) == len(xs)

        def get_val(vi):
            if vi < xn:
                return Real(float(xs[t][vi]))
            ui = vi - xn
            val = float(us[t][ui])
            return Real(val) if ui != 1 else Real(-val)

        for t in range(time_horizon):
            # filter points to be verified.
            if t % 100 != 0:
                continue
            # embed x vars with u vars
            xu = {
                v : get_val(vi)
                for vi, v in enumerate(smt_vars)
            }
            points.append(SimulationPoint(xu, t=t))
        return points

    #points = generate_points_from_grid(max_abs_val=200, step=100)
    points = generate_points_from_simulation(simul_file)

    verified_points = []
    tested_points_nr = 0

    for x in points:
        stability_hs_logger.info(f"Try nr {tested_points_nr}... {x}")
        tested_points_nr += 1
        verified = verify_stability_aux(config, dyn_systems,
                                        stable, lyap,
                                        switching_predicate, x.get())
        if verified == Result.STABLE:
            stability_hs_logger.info(f"Verified!")
            verified_points.append(x)
        if verified == Result.UNSTABLE:
            stability_hs_logger.info(f"NOT stable!")
        if verified == Result.UNKNOWN:
            stability_hs_logger.info(f"Unknown")

        if tested_points_nr % 10 == 0:
            stability_hs_logger.info(
                f"...tried {tested_points_nr}, verified {len(verified_points)}"
            )

    stability_hs_logger.critical(f"Tried with {tested_points_nr} points.")
    if not verified_points:
        stability_hs_logger.error(f"Exhausted nr of attempts. NOT verified.")
    else:
        stability_hs_logger.info(f"Verified {len(verified_points)} points.")
        for p in verified_points:
            stability_hs_logger.debug(p.str_point())

    return verified

def sample_stability(mod, ctl, refs, new_solver_f, gas_optss, simul_file):
    # x independent phase:
    # find a Lyapynov function
    config, dyn_systems, switching_predicate, _, _ = build_dyn_systems(
        mod, ctl, refs, new_solver_f
    )

    return sample_stability_aux(config, dyn_systems, switching_predicate, gas_optss, simul_file)

def get_k_candidates(num_info_file):
    from scipy.io import loadmat
    mat = loadmat(num_info_file)
    ks = [float(mat['k0']), float(mat['k1'])]
    return ks

def find_stability_assumption(config,
                              dyn_systems,
                              switching_predicate,
                              stable, lyap,
                              num_info,
                              num_info_file):
    """
    Synthesise an assumption A(x) sufficient to ensure the switched
    system stabilizes in M0..

    dyn_systems is a 2-dimensional array of dynamical systems (for mode 0 and 1)

    switching_predicate is the predicate indicating the switching:
      - switching_predicate <= 0 for M0
      - switching_predicate > 0 for M1
      - switching_predicate = 0 is the switching surface

    Steps of the proof:

    1. Find stable points and synthesise and validate the lyapunov function f0 for mode 0 and f1 for mode 1.
       The synthesis fails if such function cannot be found (i.e., if at least one of the modes is not stable)

    2. Reason by cases on the stability points.

    CASE 2.1) both stable points are in M0.

    2.1.1. Find the "inward-pointing" region of the switching surface where the Lie derivative is negative.

    2.2.2. Find a level set L0 of f0 enclosing the inward-pointing region

    2.2.2. Find a level set L1 of f1 that is contained in the above level set.

    CASE 2.2) stable point of M0 in M0, stable point of M1 is in M1.

    TODO
    """

    assert(len(dyn_systems) == 2)

    delta = Fraction(1,1000)

    switching_surface = Equals(switching_predicate, Real(0))
    m0_invar = LE(switching_predicate, Real(0))
    m1_invar = GT(switching_predicate, Real(0))

    solver = config.solver_function()
    s0_in_m0 = solver.is_sat(m0_invar.substitute(stable[0]))
    s1_in_m0 = solver.is_sat(m0_invar.substitute(stable[1]))
    
    ks = [None, None]
    if num_info_file:
        ks = get_k_candidates(num_info_file)

    if (s0_in_m0 and s1_in_m0):
        num_info.lies = [0, 0]
        # CASE 2.1
        stability_hs_logger.info("CASE 2.1 - all stable in m0")

        beta = find_inward_region(dyn_systems[0], switching_predicate)
        
        # Find k0 such that (lyap[0] <= k0 & switching_surface) -> beta
        s = time.time()
        l0_le_k0 = find_level_set(config, lyap[0], switching_surface, beta,
                                  delta,
                                  None,
                                  None,
                                  num_info, mode=0,
                                  k_init = ks[0])
        s1 = time.time()
        logging.critical(f"Time for computing level set 0: {round(s1 - s, 2)}")


        # Find k1 such that (lyap[1] <= k1 & switching_surface) -> lyap[0] <= k0
        s = s1
        l1_le_k1 = find_level_set(config, lyap[1], switching_surface,
                                  And(l0_le_k0, beta),
                                  delta,
                                  None,
                                  None,
                                  num_info, mode=1,
                                  k_init = ks[1])
        s1 = time.time()
        logging.critical(f"Time for computing level set 1: {round(s1 - s, 2)}")

        assumption = Or(And(l0_le_k0, m0_invar), And(l1_le_k1, m1_invar)).simplify()

        crosses0 = solver.is_sat(And(l0_le_k0, m1_invar))
        if crosses0: 
            logging.critical('Level set of M0 intersects M1')
        else:
            logging.critical('Level set of M0 DOES NOT intersect M1')
        
        crosses1 = solver.is_sat(And(l1_le_k1, m1_invar))
        if crosses1:
            logging.critical('Level set of M1 intersects M1')
        else:
            logging.critical('Level set of M1 DOES NOT intersect M1')

    elif (s0_in_m0 and not s1_in_m0):
        num_info.lies = [0, 1]
        # CASE 2.2
        stability_hs_logger.info("CASE 2.2 - m0 stable in m0, m1 stable in m1")

        beta0 = find_inward_region(dyn_systems[0], switching_predicate)
        # Find k0 such that (lyap[0] <= k0 & switching_surface) -> beta0
        s = time.time()
        l0_le_k0 = find_level_set(config, lyap[0], switching_surface, beta0,
                                  delta,
                                  None,
                                  None,
                                  num_info, mode=0,
                                  k_init = ks[0])
        s1 = time.time()
        logging.critical(f"Time for computing level set 0: {round(s1 - s, 2)}")


        beta1 = find_inward_region(dyn_systems[1], -switching_predicate)
        # Find k1 such that (lyap[1] <= k0 & switching_surface) -> beta1
        s = time.time()
        l1_le_k1 = find_level_set(config, lyap[1], switching_surface, beta1,
                                  delta,
                                  None,
                                  None,
                                  num_info, mode=1,
                                  k_init = ks[1])
        s1 = time.time()
        logging.critical(f"Time for computing level set 0: {round(s1 - s, 2)}")

        assumption = Or(And(l0_le_k0, m0_invar), And(l1_le_k1, m1_invar)).simplify()

        crosses0 = solver.is_sat(And(l0_le_k0, m1_invar))
        if crosses0: 
            logging.critical('Level set of M0 intersects M1')
        else:
            logging.critical('Level set of M0 DOES NOT intersect M1')
        
        crosses1 = solver.is_sat(And(l1_le_k1, m0_invar))
        if crosses1:
            logging.critical('Level set of M1 intersects M0')
        else:
            logging.critical('Level set of M1 DOES NOT intersect M0')

    else:
        stability_hs_logger.warning("The stability point of m[0] is in m[1]!")

        # DEBUG CODE
        # print("m0 region ", m0_invar.serialize())
        # print("Eq point for m0: "),
        # for k,v in stable[0].items():
        #     print("\t %f" % float(Fraction(v.serialize())))

        # print("m0 region on equilibrim ", m0_invar.substitute(stable[0]).serialize())

        # evalpred = dyn_systems[0].get_derivator().simplify(m0_invar.substitute(stable[0]).args()[0])
        # print(evalpred)

        stability_hs_logger.info("The stability point of m[0] is in m[1]!")
        breakpoint()
        assumption = FALSE()
        raise NotImplementedError()

    if num_info:
        num_info.crosses = [crosses0, crosses1]

    return assumption, lyap