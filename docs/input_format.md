# SABBATH input formats

SABBATH uses an easily machine readable input format to specify the verification problems for dynamical and hybrid systems.


## Dynamical systems

The input file is a plain text json file, containing a list of verification problem (usually just one). Each verification problem is a json dictionary:

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

that contains the following entries

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


The input accepts formulas in the Non-linear Real Arithmetic (NRA) theory, in practice polynomials over the real numbers. Refer to the [SMT-LIB standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) for the SMT-LIB syntax.

## Hybrid systems

The input for hybrid systems is also a json file:

```json
{
  "name" : "thermostat",
  "varsDecl": ["(declare-fun x () Real)"],
  "contVars": ["(declare-fun x () Real)"],

  "locations" : {
    "1" : {
      "invar" : "(and (<= 18 x) (<= x 22))",
      "vectorField": ["(= (- x) 0)"]
    },
    "2" : {
      "invar" : "(and (<= 18 x) (<= x 21))",
      "vectorField": ["(= (+ 30 (- x)) 0)"]
    }
  },

  "init" : {
    "1" : "(and (<= 19 x) (<= x 21))",
    "2" : "false"
  },

  "edges" : {
    "1" : [{"dst" : "2", "trans" : "(and (<= x 19) (= x_next x))"}],
    "2" : [{"dst" : "1", "trans" : "(and (>= x 21) (= x_next x))"}]
  },

  "property" : "true",

  "property_by_loc" : {
    "1" : "(<= x 21.5)",
    "2" : "true"
  }

  "predicates" : ["(= (- x 21.5) 0)", "(= (- x 21) 0)"],
}
```

Similarly for a dynamical system, the file specifies a `name`, a list of variables (`varsDecl`) and among these variables a list of continuous variables (`contVars`).

The hybrid system further define:

- `locations`: a list of locations as a dictionary, where the key of the entry (e.g., `1` in the example) is a name for the location, and the value is another dictionary defining the invariant condition for the location (`invar`), as a SMT-LIB formula, and the vector field in the location (`vectorField`, similarly for a single dynamical system).

- `init`: a dictionary specifying the initial state of the system by location.

- `edges`: a dictionary specifying, for each location, a list of discrete transitions. For example, the expression:

    ```
    "1" : [{"dst" : "2", "trans" : "(and (<= x 19) (= x_next x))"}]
    ```
    
    tells that there is a single transition from location "1" to location "2", and that when the transition is taken the relation `(and (<= x 19) (= x_next x))` holds. The relation expresses condition on the values of the automaton variables before and immediately after the transition: the syntax uses the suffix `_next` to identify a variable after the transition. In the example, `(= x_next x)` specifies that the value of the variable `x` does not change after taking the transition (note how you have to explicitly specify the "frame condition").
    
- `property`: specifies a safety property that must hold in all the states

- `property_by_loc`: specifies a safety property that must hold in different locations (e.g., `"1" : "(<= x 21.5)"` says that in location `1` we have $x <= 21.5$). The system check the conjunction of `property` and `property_by_loc`. In the example above, the tool would check the property:

    $$true \land (location = 1 \implies x <= 21.5) \land (location = 2 \implies true)$$.

- `predicates`: list of predicates to use in the decomposition (as for a dynamical system).
