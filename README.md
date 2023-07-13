![Regression tests](https://github.com/smover/semialgebraic_invariants/workflows/Regression%20tests/badge.svg)

# Semi-algebraic ABstrAcTor for Hybrid systems (SABbATH)

SABBATH is a formal verification and synthesis tool for dynamical and hybrid systems jointly developed by LIX - \'Ecole Polytechnique and Fondazione Bruno Kessler (FBK).

SABBATH provides the followin main functionalities:

a. Verify invariant properties for polynomial dynamical systems (i.e., dynamical systems with a polynomial Ordinary Differential Equations)

b. Verify invariant properties for hybrid systems with polynomial dynamics

c. Synthesise lyapunov functions and for 2-mode switched affine linear system


** Contact **: Sergio Mover, LIX and Ecole Polytechnique (sergio.mover@lix.polytechnique.fr)

** References **:

- Mover, Cimatti, Griggo, Tonetta. CAV 2021

- TODO: VERDI 2023


## Installation

### Dependencies
- pysmt (https://github.com/pysmt/pysmt)
- z3 solver (https://github.com/Z3Prover/z3)
- SymPy
- Ply


### Install dependencies on ubuntu
```bash
$ sudo apt-get install python python-pip
$ pip install nose
$ pip install sympy
$ pip install pysmt
$ pip install ply
$ ~/.local/bin/pysmt-install --check
$ ~/.local/bin/pysmt-install --z3
```

## a. Verifying invariant properties for polynomial dynamical systems

## b. Verify invariant properties for hybrid systems with polynomial dynamics

## c. Synthesise lyapunov functions and for 2-mode switched affine linear system

