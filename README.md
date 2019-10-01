# Module used to check and compute barrier certificates

The module use pysmt to represent formulas and polynomials (may not be the best choice).


# Dependencies
- pysmt (https://github.com/pysmt/pysmt)
- z3 solver (https://github.com/Z3Prover/z3)
- SymPy

## Install dependencies on ubuntu
```bash
$ sudo apt-get install python python-pip
$ pip install nose
$ pip install sympy
$ pip install pysmt
$ ~/.local/bin/pysmt-install --check
$ ~/.local/bin/pysmt-install --z3
```
**Note:** depending on pip you can get the executable `pysmt-install` in `/user/local/bin`


Test if the project work as:
```bash
$ ~/.local/bin/nosetests
```


# Modules
- system.py: system representation
- lie.py: compute lie derivatives
- compute.py: computation of barrier certificates

Now the system has:
- a definition for a dynamical system
- a module to compute lie derivatives for system with polynomial dynamic
- a function to validate a barrier certificate


# Notes --- hacks for interfacing with other solver and non-linear arithmetic in pysmt

Option 1. Use uninterpreted function for trascendental functions, change the smt dumper

Classes to add/modify:
  - SmtPrinter(TreeWalker)
  - SmtDagPrinter(DagWalker)
  - SmtLibSolver(object)
      - mathsat + z3 wrapper
      - smtilib2 solver, microparser.

Option 2. Change the mathsat's interface. Link for new no transcendental function.
  - Change the converter
  - operators.py -> add new operators
  - all walkers, printers, simplifier, rewriters
