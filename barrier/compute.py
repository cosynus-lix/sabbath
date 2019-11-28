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
from pysmt.oracles import FreeVarsOracle

from pysmt.shortcuts import (
    Solver,
    Implies, And,
    LE, LT, Equals,
    Real, Int, ForAll, GT, Not, GE
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
    lie_der = get_lie(template,dyn_sys)
    f_cond3 = Implies( Equals(template,Real(0)), LT(lie_der,Real(0)) )
    
    #getting the not-free variables of the formula
    not_free = set(dyn_sys.states())
    formula = ForAll(not_free,And(f_cond1, f_cond2, f_cond3 )) 

    #getting all the variables of the formula 
    or_var = FreeVarsOracle()
    template_var = or_var.get_free_variables(template)

    #ordering the variables for qepcad as (free_var,not_free)
    free_var = template_var.difference(not_free)
    ordered_var_list = list(free_var) + list(not_free)
    str_var = variables_qepcad_format(ordered_var_list) 
    nb_free_var = len(free_var)

    #Formatting the formula for qepcad
    case = ["[Case]", "\n"+str_var , "\n" + str(nb_free_var) +"\n"]
    f = open("FormulasQepcad.txt",'w')
    for s in case:
        f.write(s)
    f.close()
    to_solve = PysmtToQepcadPrinter(formula,"FormulasQepcad.txt")

    #pipe to console cat ... ./qepcad with output stored in "GeneratedBarriers.txt"
    os.system("cat $HOME/barrier/barrier/test/FormulasQepcad.txt | $qe/bin/qepcadd +N8000000 > GeneratedBarriers.txt")
    
    #if possible return pysmt formula
    


