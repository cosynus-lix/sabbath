"""
Lexer for qepcad formulas
"""

import ply.lex as lex
import ply.yacc as yacc


keywords = ('TOK_true','TOK_false')


# Parenthesis: [], ()
# Comma
# Quantifiers E, A
# Boolean operators /\ , \/ , ~ , ==> , <== , <==>
# Relational operators: = , /= , < , > , <= , >=
# Mathematical operators: +,-,*,/,^
#
# id
# constants: true, false
# numbers

tokens = keywords + (
    'TOK_ID',
    'TOK_NUMBER',

    'TOK_COMMA',

    'TOK_PLUS',
    'TOK_MINUS',
    'TOK_TIMES',
    'TOK_DIV',
    'TOK_POWER',

    'TOK_EQ',
    'TOK_NEQ',
    'TOK_LT',
    'TOK_GT',
    'TOK_LE',
    'TOK_GE',

    'TOK_AND',
    'TOK_OR',
    'TOK_NOT',
    'TOK_IMPLIES',
    'TOK_IMPLIES_REVERSED',
    'TOK_IFF',

    'TOK_EXIST',
    'TOK_FORALL',

    'TOK_LPAREN',
    'TOK_RPAREN',

    'TOK_LSQUARE',
    'TOK_RSQUARE',
    )


# Tokens
def t_TOK_ID(t):
    r'[a-zB-DF-Z_$][a-zA-Z0-9_$<>]*'
    if "TOK_" + t.value in keywords:
        t.type = "TOK_" + t.value
    return t

def t_TOK_NUMBER(t):
    r'\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
    return t


t_TOK_COMMA = r","
t_TOK_PLUS = r"\+"
t_TOK_MINUS = r"-"
t_TOK_TIMES = r"\*"
t_TOK_DIV = r"/"
t_TOK_POWER = r"\^"

t_TOK_EQ = r"\="
t_TOK_NEQ = r"/\="
t_TOK_LT = r"<"
t_TOK_GT = r">"
t_TOK_LE = r"<="
t_TOK_GE = r">="

t_TOK_AND = r"/\\"
t_TOK_OR = r"\\/"
t_TOK_NOT = r"\~"
t_TOK_IMPLIES = r"\=\=\>"
t_TOK_IMPLIES_REVERSED = r"\<\=\="
t_TOK_IFF = r"<\=\=>"
t_TOK_EXIST = r"E"
t_TOK_FORALL = r"A"
t_TOK_LPAREN = r"\("
t_TOK_RPAREN = r"\)"
t_TOK_LSQUARE = r"\["
t_TOK_RSQUARE = r"\]"

t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

def reset():
    lexer.lineno = 1
    if lexer.lexdata is None:
        return
    tok = lexer.token()
    while (tok is not None):
        tok = lexer.token()

# Build the lexer
import ply.lex as lex
lexer = lex.lex(debug=0)

