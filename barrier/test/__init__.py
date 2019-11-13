# Barrier python module

import os
from functools import wraps

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from pysmt.environment import reset_env

class TestCase(unittest.TestCase):
    """Wrapper on the unittest TestCase class.

    This class provides setUp and tearDown methods for pySMT in which
    a fresh environment is provided for each test.
    """

    def setUp(self):
        self.env = reset_env()
        self.env.enable_infix_notation = True
