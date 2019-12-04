"""
Parser for qepcad formulas

STD ISSUE WITH THIS: it is non-rentrant

While parsing we build an AST to represent the SPEC.

WARNING: rhs of spec now is an atom, wich also contains the assign token.
What does it mean for a spec?
"""

import ply.lex as lex

from barrier.qepcad.lex import lexer
from barrier.qepcad.lex import *
from barrier.qepcad.lex import tokens

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    ForAll, Exists,
    Not, And, Or, Implies, Iff,
    LE, GE, LT, GT, Equals, NotEquals,
    Pow, Plus, Minus, Times, Div,
    Real, Int,
    Symbol, TRUE, FALSE
)



import ply.yacc as yacc
import string

precedence = (
    ('left', 'TOK_IMPLIES', 'TOK_IMPLIES_REVERSED', 'TOK_IFF'),
    ('left', 'TOK_OR'),
    ('left', 'TOK_AND'),
    ('right','TOK_NOT'),

    ('left', 'TOK_PLUS', 'TOK_MINUS'),
    ('left', 'TOK_TIMES', 'TOK_DIV'),
    ('left', 'TOK_POWER'),

    ('left', 'TOK_ID', 'TOK_NUMBER'), # fix isse with precedence and implicit operators

    ('left', 'TOK_COMMA'),
    ('left','TOK_true')
)

def p_tl_formula_prenex(t):
    ''' tl_formula : quantifiers formula
    '''

    current = t[2]
    for quant_list in t[1]:
        (qtype, vlist) = quant_list
        vlist.reverse()
        current = qtype(vlist, current)
    t[0] = current

def p_tl_formula_formula(t):
    ''' tl_formula : formula '''
    t[0] = t[1]

def p_quantifiers_base_exists(t):
    ''' quantifiers : TOK_LPAREN TOK_EXIST quantifier_vars TOK_RPAREN '''
    t[0] = [(Exists, t[3])]

def p_quantifiers_base_forall(t):
    ''' quantifiers : TOK_LPAREN TOK_FORALL quantifier_vars TOK_RPAREN '''
    t[0] = [(ForAll, t[3])]

def p_quantifiers_exists(t):
    ''' quantifiers : TOK_LPAREN TOK_EXIST quantifier_vars TOK_RPAREN quantifiers '''
    quant_list = [(Exists, t[3])]
    t[0] = t[5] + quant_list

def p_quantifiers_forall(t):
    ''' quantifiers : TOK_LPAREN TOK_FORALL quantifier_vars TOK_RPAREN quantifiers '''
    quant_list = [(ForAll, t[3])]
    t[0] = t[5] + quant_list

def p_quantifier_vars_base(t):
    ''' quantifier_vars : TOK_ID '''
    t[0] = [Symbol(t[1], REAL)]

def p_quantifier_vars(t):
    ''' quantifier_vars : TOK_ID TOK_COMMA quantifier_vars
    '''
    var = [Symbol(t[1], REAL)]
    t[0] = t[3] + var


def p_formula_true(t):
    ''' formula : TOK_true
    '''
    t[0] = TRUE()

def p_formula_false(t):
    ''' formula : TOK_false
    '''
    t[0] = FALSE()


def p_formula_pred(t):
    ''' formula : predicate
                | TOK_LSQUARE formula TOK_RSQUARE
    '''
    if 2 == len(t):
        t[0] = t[1]
    else:
        t[0] = t[2]

def p_formula_not(t):
    ''' formula : TOK_NOT formula '''
    t[0] = Not(t[2])

def p_formula_and(t):
    ''' formula : formula TOK_AND formula '''
    t[0] = And(t[1], t[3])

def p_formula_or(t):
    ''' formula : formula TOK_OR formula '''
    t[0] = Or(t[1], t[3])

def p_formula_implies(t):
    ''' formula : formula TOK_IMPLIES formula '''
    t[0] = Implies(t[1], t[3])

def p_formula_iff(t):
    ''' formula : formula TOK_IFF formula '''
    t[0] = Iff(t[1], t[3])

def p_formula_implies_reversed(t):
    ''' formula : formula TOK_IMPLIES_REVERSED formula '''
    t[0] = Implies(t[3], t[1])

def p_predicate_eq(t):
    ''' predicate : expr TOK_EQ expr'''
    t[0] = Equals(t[1], t[3])

def p_predicate_neq(t):
    ''' predicate : expr TOK_NEQ expr'''
    t[0] = NotEquals(t[1], t[3])

def p_predicate_lt(t):
    ''' predicate : expr TOK_LT expr'''
    t[0] = LT(t[1], t[3])

def p_predicate_gt(t):
    ''' predicate : expr TOK_GT expr'''
    t[0] = GT(t[1], t[3])

def p_predicate_le(t):
    ''' predicate : expr TOK_LE expr'''
    t[0] = LE(t[1], t[3])

def p_predicate_ge(t):
    ''' predicate : expr TOK_GE expr'''
    t[0] = GE(t[1], t[3])

def p_expr_id(t):
    ''' expr : TOK_ID
    '''
    t[0] = Symbol(t[1], REAL)

def p_expr_number(t):
    ''' expr : TOK_NUMBER
    '''
    t[0] = Real(int(t[1]))

def p_expr_par(t):
    ''' expr : TOK_LSQUARE expr TOK_RSQUARE '''
    t[0] = t[2]

def p_expr_plus(t):
    ''' expr : expr TOK_PLUS expr '''
    t[0] = Plus(t[1], t[3])

def p_expr_minus(t):
    ''' expr : expr TOK_MINUS expr '''
    t[0] = Minus(t[1], t[3])

def p_expr_times(t):
    ''' expr : expr TOK_TIMES expr '''
    t[0] = Times(t[1], t[3])

def p_expr_times_implicit(t):
    ''' expr : expr expr '''

    t[0] = Times(t[1], t[2])


def p_expr_div(t):
    ''' expr : expr TOK_DIV expr '''
    t[0] = Div(t[1], t[3])

def p_expr_power(t):
    ''' expr : expr TOK_POWER TOK_NUMBER '''

    exp = Real(int(t[3]))
    t[0] = Pow(t[1], exp)




def p_error(t):
    for handler in handlers:
        if (t is not None):
            handler.set_in_error(t.value, t.lineno)
        else:
            handler.set_in_error("unknown", -1)

handlers = []

parser = yacc.yacc(debug=2)

class QepcadParser(object):
    """ Parse a qepcad formula
    """

    def __init__(self, parser):
        self.parser = None
        self.in_error = False
        self.error_value = None
        self.error_line = -1

    def parse(self, qepcad_str):
        self.in_error = False
        pysmt_formula = parser.parse(qepcad_str)
        if (self.in_error): pysmt_formula = None
        return pysmt_formula

    def set_in_error(self, t_value, t_lineno):
        # print("Syntax error at '%s' at line %d." % (t_value, t_lineno))

        # store the error status
        self.in_error = True
        self.error_value = t_value
        self.error_line = t_lineno



qepcad_parser = QepcadParser(parser)
handlers.append(qepcad_parser)
