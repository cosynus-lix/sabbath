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
import barrier.printers

from pysmt.shortcuts import (
    Solver,
    Implies, And,
    LE, LT, Equals,
    Real
)

from pysmt.logics import QF_NRA

import logging


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
    lie_der = get_lie(barrier, dyn_sys)
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
    template of polynomial form
    """
    formula = And(Implies(init, LE(template, 0)), Implies(LE(template,0),safe), 
                Implies( Equals(template,0), LT(Lie(dyn_sys, template),0)) )
    
    to_solve = barrier.printers.PysmtToQepcadPrinter(formula)

    return to_solve 
    
    


