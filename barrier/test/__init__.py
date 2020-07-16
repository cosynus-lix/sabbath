# Barrier python module

import os
import logging
import sys

from functools import wraps

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from pysmt.environment import reset_env
from pysmt.exceptions import SolverAPINotFound

from barrier.msatic3 import MSatic3
from barrier.mathematica.mathematica import has_kernel

class TestCase(unittest.TestCase):
    """Wrapper on the unittest TestCase class.

    This class provides setUp and tearDown methods for pySMT in which
    a fresh environment is provided for each test.
    """

    def setUp(self):
        self.env = reset_env()
        self.env.enable_infix_notation = True

    def get_from_path(self, path, must_exists=True):
        current_path = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(current_path, path)
        self.assertTrue((not must_exists) or os.path.exists(input_path))
        return input_path


    def log_to_stdout(self):
        root = logging.getLogger()
        root.setLevel(logging.DEBUG)
        handler = logging.StreamHandler(sys.stdout)
        handler.setLevel(logging.DEBUG)
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        handler.setFormatter(formatter)
        root.addHandler(handler)


class skipIfMSaticIsNotAvailable(object):
    """Skip a test if the given solver is not available."""

    def __init__(self):
        pass

    def __call__(self, test_fun):
        msg = "MSatic3 not available"
        # cond = MSatic3.find_msatic() is None
        @unittest.skipIf(True, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfMathematicaIsNotAvailable(object):
    """Skip a test if mathematica is not available."""

    def __init__(self):
        self.has_kernel = has_kernel()
        pass

    def __call__(self, test_fun):
        msg = "Mathematica not available"
        skip = self.has_kernel
        @unittest.skipIf(skip, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper

