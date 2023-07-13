## num_modes is the number of modes.
## num_controllers is the number of controller variables.
## num_variables is the number of variables
## num_outputs is the number of outputs
## reference_values is a column vector that represents the reference values.
# For mode i, we have:
## A_i, B_i, C_i: 
the matrices that define the system:

x' = Ax + Bu;
y = Cx;

## KP_i, KI_i:
The values of the PI controllers

## Guard_i:
A matrix with "num_variables + 1" columns and a variable number of row.
Each row represents a linear guard. The row j stands for the inequality

Guard_i(j, :) * [x ; 1] < 0.
 
We need to address the problem of < or <=.