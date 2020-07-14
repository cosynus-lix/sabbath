# Verify properties for polynomial dynamical systems

The module use pysmt to represent formulas and polynomials (may not be the best choice).


# Dependencies
- pysmt (https://github.com/pysmt/pysmt)
- z3 solver (https://github.com/Z3Prover/z3)
- SymPy
- Ply


## Install dependencies on ubuntu
```bash
$ sudo apt-get install python python-pip
$ pip install nose
$ pip install sympy
$ pip install pysmt
$ pip install ply
$ ~/.local/bin/pysmt-install --check
$ ~/.local/bin/pysmt-install --z3
```
