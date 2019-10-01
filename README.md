# Module used to check and compute barrier certificates

The module use pysmt to represent formulas and polynomials (may not be the best choice).


# Dependencies
- pysmt (https://github.com/pysmt/pysmt)
- z3 solver (https://github.com/Z3Prover/z3)

Install z3 on your system from github and not from pysmt (due to this bug: https://github.com/pysmt/pysmt/issues/603)

# Modules

- system.py: system representation
- lie.py: compute lie derivatives
- compute.py: computation of barrier certificates

Now the system has:
- a definition for a dynamical system
- a module to compute lie derivatives for system with polynomial dynamic
- a function to validate a barrier certificate




# Notes --- hack for interfacing with other solver and non-linear arithmetic in pysmt
- uninterpreted function + smt dumper modificato
  - All modified - inherit, modify/add
  - SmtPrinter(TreeWalker)
  - SmtDagPrinter(DagWalker)
  - class SmtLibSolver(object)
      - mathsat + z3 wrapper
      - smtilib2 solver, microparser.

  - mathsat - link for new no transcendental
    - converter
    - operators.py -> add operator
      - all walkers, printers, simplifier, rewriters
