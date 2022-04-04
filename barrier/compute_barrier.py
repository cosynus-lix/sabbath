# - *- coding: utf- 8 - *-

""" Functions to check and synthesise barrier certificates.

1. Check of barrier certificate

The input of the problem are:
  - a dynamical system
  - a set of initial states
  - a set of safe states
  - a candidate barrier certificate function

The output of the problem are:
  - True iff the function is a barrier certificate
  - a counter-example, if the candidate is not a barrier certificate
  The counter-example is a state of the system where the candidate
  is not a barrier certifièacate

Now we check the "basic" barrier certificate.
Other certiticates can be the exponential barrier certificate or a
barrier certificate containing more polynomials.

2. Synthesis problem

"""

from barrier.system import DynSystem
from barrier.printers import PysmtToQepcadPrinter
from barrier.qepcad.driver import QepcadDriver
from pysmt.oracles import FreeVarsOracle

from barrier.utils import gen_template, get_new
from barrier.sympy_utils import gen_template_sympy

from pysmt.shortcuts import (
    Solver,
    Implies, And,
    LE, LT, Equals,
    Real, Int, ForAll, GT, Not,
    GE, LE
)
from pysmt.logics import QF_NRA
from pysmt.rewritings import nnf, conjunctive_partition

import picos
try:
    from SumOfSquares import SOSProblem
except ImportError:
    def SOSProblem():
        raise Exception("SumOfSquare module not found")


import logging
import os

def is_barrier(dyn_sys, init, safe, barrier):
    """
    Check that:
    1) init -> barrier <= 0
    2) barrier <= 0 -> safe
    3) barrier = 0 -> Lie(sys, barrier) < 0
    """

    solver = Solver(logic=QF_NRA, name="z3")

    # 1. init -> cert <= 0
    in_init = Implies(init, LE(barrier, Real(0)))

    # 2. barrier <= 0 -> Safe
    in_safe = Implies(LE(barrier, Real(0)), safe)

    # 3. barrier = 0 -> lie_derivative < 0
    derivator = dyn_sys.get_derivator()
    lie_der = derivator.get_lie_der(barrier)
    consecution = Implies(Equals(barrier, Real(0)),
                          LT(lie_der, Real(0)))

    logging.debug("Barrier certificate computation")
    logging.debug(str(dyn_sys))
    logging.debug("Barrier: " + str(barrier.serialize()))
    logging.debug("Lie der: " + str(lie_der.serialize()))
    logging.debug("Init: " + str(init.serialize()))
    logging.debug("Safe: " + str(safe.serialize()))

    if (not solver.is_valid(in_init)):

        logging.debug("Barrier does not contain initial states\n"
                      "--- counter-example to induction:")
        logging.debug(solver.get_model())

        return False
    elif (not solver.is_valid(in_safe)):

        logging.debug("Barrier intersect unsafe states\n"
                      "--- counter-example to induction:")
        logging.debug(solver.get_model())

        return False
    elif (not solver.is_valid(consecution)):

        logging.debug("Barrier derivative is not negative on borders\n"
                      "--- counter-example to induction:")
        logging.debug(solver.get_model())

        return False
    else:
        return True



def barrier_generator(dyn_sys,init, safe,template):
    """ Generates a barrier certificate by using qepcad solver
    and :   1) init -> barrier <= 0
            2) barrier <= 0 -> safe
            3) barrier = 0 -> Lie(sys, barrier) < 0
    template = polynomial formula
    """

    def variables_qepcad_format(list_var):
        str_var = "("
        for i in range(len(list_var)-1):
            str_var = str_var+str(list_var[i])+","
        str_var = str_var+str(list_var[-1])+")"
        return str_var


    # 1st condition on barrier
    f_cond1 = Implies(init,LE(template,Real(0)))

    #2nd condition
    f_cond2 = Implies(LE(template,Real(0)),safe)

    #3rd condition
    derivator = dyn_sys.get_derivator()
    lie_der = derivator.get_lie_der(template)
    f_cond3 = Implies( Equals(template,Real(0)), LT(lie_der,Real(0)) )

    #getting the not-free variables of the formula
    not_free = set(dyn_sys.states())
    formula = ForAll(not_free,And(f_cond1, f_cond2, f_cond3 ))

    #getting all the variables of the formula
    or_var = FreeVarsOracle()
    template_var = or_var.get_free_variables(template)

    #ordering the variables for qepcad as (free_var,not_free)
    free_var = template_var.difference(not_free)
    result = QepcadDriver.call_qepcad(formula, free_var, not_free)

    # Get the value for the unnkonwn variables
    # Must solve the formula in P-s to find an assignment.
    # The formula may still be unsatisfiable
    solver = Solver(logic=QF_NRA, name="z3")

    if (solver.is_sat(result)):
        # There is an assignment to the Ps.
        # Instantiate the parameter
        model = solver.get_model()
        sigma = {v: model[v] for v in free_var}
        sub_template = template.substitute(sigma).simplify()
        return sub_template
    else:
        # the template is not enough to find a barrier
        return FALSE()


def synth_barrier_sos(get_new, vars_list,
                      barrier_template,
                      coefficients,
                      init_preds,
                      bad_preds,
                      barrier_lie,
                      degree,
                      _lambda = 0,
                      eps = 0.001):
    """
    We use the exponential condition for the dynamical system

    Kong, Hui, et al. "Exponential-condition-based barrier certificate generation for safety verification of hybrid systems." CAV 2013
    """
    # Generate a barrier certificate
    prob = SOSProblem()

    assert (_lambda <= 0 and _lambda >= -1)

    # barrier <= on initial states
    # - barrier - sum_{i \in Init}{poly * i} >= 0
    init_condition = - barrier_template
    for init in init_preds:
        IP_init, coefficients_init = gen_template_sympy(get_new, vars_list, degree, 0)
        prob.add_sos_constraint(IP_init, vars_list)
        init_condition = init_condition -(IP_init * init) 
    prob.add_sos_constraint(init_condition, vars_list)

    # barrier > 0 on bad states
    # barrier - sum_{b \in Bad}{poly * b} - epsilon >= 0
    bad_condition = barrier_template - eps
    for bad in bad_preds:
        IP_bad, coefficients_bad = gen_template_sympy(get_new, vars_list, degree, 0)
        prob.add_sos_constraint(IP_bad, vars_list)
        bad_condition = bad_condition - IP_bad * bad
    prob.add_sos_constraint(bad_condition, vars_list)

    # the lie derivative of the barrier always decreases
    # lambda * barrier - barrier' >= 0
    lie_condition = _lambda * barrier_template - barrier_lie
    prob.add_sos_constraint(lie_condition, vars_list)

    sol = prob.solve(primals=None)

    if (sol.problemStatus == picos.modeling.solution.PS_FEASIBLE):
        new_template = barrier_template
        for s in coefficients:
            c = prob.sym_to_var(s)
            # convert floating point to rationals
            val = round(c.value, 5)
            sympy_value = sp.nsimplify(sp.sympify(val), rational=True)
            #print("%s, %s (%s)" % (s, c, str(c.value)))
            new_template = new_template.subs(s, sympy_value)
        return (True, new_template)
    else:
        # None or False
        return (False, None)



def synth_barrier(dyn_sys, init, bad, degree):
    def process_f(f):
        """
        Assume f is a conjunction of predicates p >= 0.

        Raise an exception if that's not the case, transform the predicate
        and returns a list of predicates p >=0 otherwise
        """

        epsilon = 0.0001
        acc = []
        for p in conjunctive_partition(f):
            if p.is_le():
                polynomial = p.args()[1] - p.args()[0]
                acc.append(polynomial)
            elif p.is_lt():
                # arbitrary epsilon
                polynomial = p.args()[1] - p.args()[0] - epsilon
                acc.append(polynomial)
            elif p.is_equals():
                acc.append(p.args()[1] - p.args()[0])
                acc.append(p.args()[0] - p.args()[1])
            else:
                raise Exception("Unexpected operator in %s" % str(p))

        return acc

    vars_list = [s for s in dyn_sys.states()]

    (barrier_template, coefficients) = gen_template(dyn_sys, degree)
    derivator = dyn_sys.get_derivator()
    barrier_derivative = derivator.get_lie_der(barrier_template)

    get_new_inst = lambda : get_new(derivator)


    # preprocess init and bad
    # we assume init and bad to be a conjunction of predicates P >= 0
    init_pred = process_f(nnf(init))
    bad_pred = process_f(nnf(bad))

    (res, barrier) = synth_barrier_sos(
        get_new_inst,
        [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
        derivator._get_sympy_expr(barrier_template),
        [derivator._get_sympy_expr(v) for v in coefficients],
        [derivator._get_sympy_expr(i) for i in init_pred],
        [derivator._get_sympy_expr(b) for b in bad_pred],
        derivator._get_sympy_expr(barrier_derivative),
        degree
    )

    if not barrier is None:
        barrier = derivator._get_pysmt_expr(barrier)

    return (res, barrier)
