# SABBATH input formats

SABBATH uses an easily machine readable input format to specify the verification problems for dynamical and hybrid systems.



## Dynamical systems

The input file is a plain text json file, containing a list of verification problem (usually just one).

Each verification problem is a json dictionary, containing the following entries:

- `varsDecl`: *list* of variable declarations. The list should declare all the continuous variable of the system (i.e., the variables that evolves continuously in time) and the possible parameters (i.e., variables that do not change in time and have an unknown, but fixed, value in the system).

    The variable declaration follows the SMT2-lib format and uses the SMT2-lib types (here you should always use the `Real` type).
    
    An example of variable declaration is: `(declare-fun _y () Real)` to declare a variable called `_y`.


- `contVars`: *list* of the *continuous variables* of the system. This list cannot contain elements that are not in the list `varsDecl` of all the variables.

    *IMPORTANT*: the declaration order in this list is important when declaring the vector field associated to each variable (the association is done using the position of the variable in the this list).

- `antecedent`: SMT2-lib formula specifying the *initial* states

- `consequent`: SMT2-lib formula specifying the *safe* states (i.e., the invariant property)

- `constraints`: SMT2-lib formula specifying the continuous invariant (i.e., the analysis assumes the system never exits such set of states)

- `name`: mnemonic name for the problem (can be whatever string)

- `vectorField`: list declaring the vector field for the continuous variable. The vector field specifies a system of Ordinary Differential Equations associating to the derivative of each continuous variable a polynomial.

    For example, the derivative for $\dot{x}$ is $-2y$ and is written with the expression:
    
    $$(= (* (- 2)  y) 0)$$
    
    *NOTE*: the input requires an equality in SMT2-lib, even if the expected input is a polynomial. The tool will only use the left-hand side of the equality, $(* (- 2)  y)$ as polynomial (this format is not clean and a quick hack for using the SMT2-lib parser).

- `predicates`: the list of *polynomials* to use for the semi-algebraic decomposition. Each element in the list describe a polynomial of the abstraction, written as an equality to 0 (the tool will take the left-hand side of the equality as polynomial, as for the vector fields).


Here's a complete example of an input problem:

```json
[{
  "varsDecl": ["(declare-fun _y () Real)", "(declare-fun _x () Real)"],
  "contVars": ["(declare-fun _y () Real)", "(declare-fun _x () Real)"],
  "antecedent": "(and (> (+ _x 2) 0) (<= 0 (+ _x (- _y) (- 0.5))))",
  "consequent": "(> (+ (* (+ _x 2) (+ _x 2)) (* (+ _y 0.0) (+ _y 0.0)) (- 1) ) 0)",
  "constraints": "true",
  "name": "Liu Zhan Zhao Emsoft11 Example 25 new example",
  "predicates": [
    "(= (+ _x (- _y) (- 0.5)) 0)",
    "(= (+ _x _y 0.5) 0)",
    "(= (+ _x 2) 0)"
],

  "vectorField": ["(= (* _x (* _x 1)) 0)", "(= (* (- 2) _y) 0)"]
}]

```

## Hybrid systems

