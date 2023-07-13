![Regression tests](https://github.com/smover/semialgebraic_invariants/workflows/Regression%20tests/badge.svg)

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
$ pip install numpy
$ pip install scipy
$ pip install picos
$ pip install control
$ ~/.local/bin/pysmt-install --check
$ ~/.local/bin/pysmt-install --z3
```

