"""
Utility functions
"""

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    Symbol, TRUE, FALSE,
    Real,
    And,
    LE
)


def get_range(var_list, range_matrix):
    """
    Generates a box constraints.
    """

    var_range = TRUE()

    assert(len(range_matrix) == len(var_list))

    for i in range(len(var_list)):
        assert(2 == len(range_matrix[i]))

        var = var_list[i]
        lower = range_matrix[i][0]
        upper = range_matrix[i][1]

        var_range = And(var_range,
                        And(LE(lower, var),
                            LE(var, upper)))

    return var_range
