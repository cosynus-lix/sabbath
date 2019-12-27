""" Test the specification parser

"""

import logging

try:
    import unittest2 as unittest
except ImportError:
    import unittest
from barrier.test import TestCase

from ply.lex import LexToken
import ply.yacc as yacc

try:
    from StringIO import StringIO
except ImportError:
    from io import StringIO

from barrier.qepcad.lex import lexer, reset
from barrier.qepcad.parser import qepcad_parser


class TestSpecParser(TestCase):

    def setUp(self):
        reset()

    @staticmethod
    def new_tok(lexpos, tok_type, lineno, value):
        # Create a token for return
        tok = LexToken()
        tok.value = value
        tok.lineno = lineno
        tok.lexpos = lexpos
        tok.type = tok_type
        return tok

    def _test_multiple_token(self, token_list, string):
        # clean the lexer state
        # for f in lexer: None

        lexer.input(string)

        i = 0
        tok = lexer.token()
        while (tok is not None):
            # print("Lexed " + str(tok.value))
            # print("Expected " + str(token_list[i].value))
            # print("Lexed " + str(tok.type))
            # print("Expected " + str(token_list[i].type))

            if i > len(token_list):
                raise Exception("Found more tokens than expeced")
            self.assertTrue(tok.value == token_list[i].value)
            self.assertTrue(tok.lineno == token_list[i].lineno)
            self.assertTrue(tok.lexpos == token_list[i].lexpos)
            self.assertTrue(tok.type == token_list[i].type)

            i = i + 1
            tok = lexer.token()

        # did not parse anything else
        with self.assertRaises(StopIteration):
            lexer.next()

    def _test_single_token(self, lexpos, tok_type, lineno, value, string):
        tok_ref = TestSpecParser.new_tok(lexpos,tok_type,lineno,value)
        return self._test_multiple_token([tok_ref], string)


    def test_lexer(self):
        self._test_single_token(0,'TOK_ID',1,'ciao','ciao')
        self._test_single_token(0,'TOK_ID',1,'x2','x2')
        self._test_single_token(0,'TOK_NUMBER',1,2,'2')

        self._test_single_token(0, 'TOK_PLUS', 1, '+', '+')
        self._test_single_token(0, 'TOK_MINUS', 1, '-', '-')
        self._test_single_token(0, 'TOK_TIMES', 1, '*', '*')
        self._test_single_token(0, 'TOK_DIV', 1, '/', '/')
        self._test_single_token(0, 'TOK_POWER', 1, '^', '^')

        self._test_single_token(0, 'TOK_EQ', 1, '=', '=')
        self._test_single_token(0, 'TOK_NEQ', 1, '/=', '/=')
        self._test_single_token(0, 'TOK_LT', 1, '<', '<')
        self._test_single_token(0, 'TOK_GT', 1, '>', '>')
        self._test_single_token(0, 'TOK_LE', 1, '<=', '<=')
        self._test_single_token(0, 'TOK_GE', 1, '>=', '>=')

        self._test_single_token(0, 'TOK_NOT', 1, '~', '~')
        self._test_single_token(0, 'TOK_AND', 1, '/\\', '/\\')
        self._test_single_token(0, 'TOK_OR', 1, '\\/', '\\/')
        self._test_single_token(0, 'TOK_IMPLIES', 1, '==>', '==>')
        self._test_single_token(0, 'TOK_IMPLIES_REVERSED', 1, '<==', '<==')
        self._test_single_token(0, 'TOK_IFF', 1, '<==>', '<==>')

        self._test_single_token(0, 'TOK_EXIST', 1, 'E', 'E')
        self._test_single_token(0, 'TOK_FORALL', 1, 'A', 'A')

        self._test_single_token(0, 'TOK_COMMA', 1, ',', ',')

        self._test_single_token(0, 'TOK_LPAREN', 1, '(', '(')
        self._test_single_token(0, 'TOK_RPAREN', 1, ')', ')')


        self._test_single_token(0, 'TOK_true', 1, 'true', 'true')
        self._test_single_token(0, 'TOK_false', 1, 'false', 'false')


        # TestSpecParser.new_tok(lexpos,tok_type,lineno,value)
        res = [TestSpecParser.new_tok(0,'TOK_ID',1,'l'),
               TestSpecParser.new_tok(1,'TOK_COMMA',1,','),
               TestSpecParser.new_tok(2,'TOK_ID',1,'l'),
               TestSpecParser.new_tok(3,'TOK_LPAREN',1,'('),
               TestSpecParser.new_tok(4,'TOK_RPAREN',1,')')]
        self._test_multiple_token(res, "l,l()"),

    def _test_parse(self, formula):
        res = qepcad_parser.parse(formula)
        self.assertTrue(res is not None)
        return res

    def _test_parse_error(self, formulas):
        res = qepcad_parser.parse(formulas)
        self.assertTrue(res is None)

    def test_parser(self):
        correct_expr = ["[x1 > x2]",
                        "(E x1)[x1 > x2]",
                        "(A x1)[x1 > x2]",
                        "(A x1)(E x2)[x1 > x2]",
                        "(A x1, x2, x3)(E x2, x3)[x1 > x2]",
                        "[x1 + 3 > 0]",
                        "[3 > 0]",
                        "[3 = 0]",
                        "[3 = 0 /\ 3 + x1 >= 7]",
                        "[3 = 0 /\ 3 + x1 >= 7 \/ x1 - x3 <= 22]",
                        "[x1 - x3 <= 22/3]",
                        "[x1^2 - x3 <= 22/3]",
                        "[x1^2 - x3 <= 22/3 ==> [[x1 >= 23]]]",
                        "[x1^2 - x3 <= 22/3 <==> [[x1 >= 23]]]",
                        "[x1^2 - x3 <= 22/[x3/x3]]",
                        "[p - 2 >= 0]",
                        "p - 2 >= 0",
                        "p^2 - 8 p + 4 < 0",
                        "p - 2 >= 0 /\ p^2 - 8 p + 4 < 0"
        ]

        for expr in correct_expr:
            self._test_parse(expr)

        wrong_expr = ["[x1]",
                      "1 + 3",
                      "[x1^x2 - x3 <= 22/3]",
        ]

        for expr in wrong_expr:
            self._test_parse_error(expr)

        # Test some of the operator's precendences
        check_res = [("p p^2 p < 2", "((p * ((p ^ 2.0) * p)) < 2.0)"),
                     ("p^2 +2 p < 2", "(((p ^ 2.0) + (2.0 * p)) < 2.0)"),
                     (" p^2 +2 2 < 2", "(((p ^ 2.0) + (2.0 * 2.0)) < 2.0)")]

        for (a,b) in check_res:
            res = self._test_parse(a)
            self.assertTrue(str(res) == b)

