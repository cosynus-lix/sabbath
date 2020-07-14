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
from barrier.lie import get_lie
from barrier.printers import PysmtToQepcadPrinter
from barrier.qepcad.driver import QepcadDriver
from pysmt.oracles import FreeVarsOracle

from pysmt.shortcuts import (
    Solver,
    Implies, And,
    LE, LT, Equals,
    Real, Int, ForAll, GT, Not,
    GE, LE
)
from pysmt.logics import QF_NRA

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

