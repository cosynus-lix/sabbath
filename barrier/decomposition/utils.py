"""
Common utils for computing/encoding the algebraic decomposition.

"""

from barrier.lie import Pysmt2Sympy, Sympy2Pysmt

def get_poly_from_pred(pred):
    poly = None

    assert(pred.is_equals() or
           pred.is_le() or
           pred.is_lt())

    # left-hand side - right-hand side
    poly = pred.args()[1] - pred.args()[0]

    return (poly, pred.node_type())

def get_unique_poly_list(poly_list):
    """
    The algebraic decomposition obtained with a polynomial p and with -p are the
    same.

    We want to just keep one of p here.
    """

    pysmt2sympy = Pysmt2Sympy()
    sympy2pysmt = Sympy2Pysmt()

    poly_set = set()
    new_poly_list = []
    for p in poly_list:
        sympy_p = (pysmt2sympy.walk(p)).expand()
        sympy_minus_p = (- sympy_p).expand()

        if (not ((sympy_p in poly_set) or
                 (sympy_minus_p in poly_set))):
            new_poly_list.append(p)
            poly_set.add(sympy_p)
            poly_set.add(sympy_minus_p)

    return new_poly_list
