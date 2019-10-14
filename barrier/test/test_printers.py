import unittest

from pysmt.shortcuts import (
        Implies, GE )

from barrier.printers import QepcadPrinter

class testprint(TestCase):
    def test_printer(self):
        formula = Implies( GE(x1+x2,0), GE( x1, -x2))
        res = PysmtToQepcadPrinter(formula)
        exp = "[x1+x2 >= 0 ==> x1 >= -x2]."
        self.assertTrue( res==exp)

