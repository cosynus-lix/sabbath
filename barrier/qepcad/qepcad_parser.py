"""
Parser for qepcad formulas

STD ISSUE WITH THIS: it is non-rentrant

While parsing we build an AST to represent the SPEC.

WARNING: rhs of spec now is an atom, wich also contains the assign token.
What does it mean for a spec?
"""

import ply.lex as lex
from barrier.qepcad.qepcad_lex import lexer
from barrier.qepcad.qepcad_lex import tokens


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

    ('left', 'TOK_COMMA'),
    ('left','TOK_true')
)

def p_tl_formula(t):
    ''' tl_formula : quantifiers formula
                   | formula
    '''
    t[0] = 1

def p_quantifiers(t):
    ''' quantifiers : TOK_LPAREN TOK_EXIST quantifier_vars TOK_RPAREN
                    | TOK_LPAREN TOK_EXIST quantifier_vars TOK_RPAREN quantifiers
                    | TOK_LPAREN TOK_FORALL quantifier_vars TOK_RPAREN
                    | TOK_LPAREN TOK_FORALL quantifier_vars TOK_RPAREN quantifiers
    '''
    t[0] = 1


def p_quantifier_vars(t):
    ''' quantifier_vars : TOK_ID
                        | TOK_ID TOK_COMMA quantifier_vars
    '''
    t[0] = 1

def p_formula(t):
    ''' formula : TOK_true
                | TOK_false
                | predicate
                | TOK_LSQUARE formula TOK_RSQUARE
                | TOK_NOT formula
                | formula TOK_AND formula
                | formula TOK_OR formula
                | formula TOK_IMPLIES formula
                | formula TOK_IMPLIES_REVERSED formula
                | formula TOK_IFF formula
    '''
    t[0] = 1


def p_predicate(t):
    ''' predicate : expr TOK_EQ expr
                  | expr TOK_NEQ expr
                  | expr TOK_LT expr
                  | expr TOK_GT expr
                  | expr TOK_LE expr
                  | expr TOK_GE expr
    '''
    t[0] = 1

def p_expr(t):
    ''' expr : TOK_ID
             | TOK_NUMBER
             | TOK_LSQUARE expr TOK_RSQUARE
             | expr TOK_PLUS expr
             | expr TOK_MINUS expr
             | expr TOK_TIMES expr
             | expr TOK_DIV expr
             | expr TOK_POWER TOK_NUMBER
    '''
    t[0] = 1

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
