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

from sabbath.vmt.vmt_engines import MSatic3, MSatic3NotAvailable, Ic3IA, Ic3IANotAvailable
from sabbath.mathematica.mathematica import has_kernel

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
        skip = False
        try:
            MSatic3()
        except MSatic3NotAvailable:
            skip = True
        @unittest.skipIf(skip, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper

class skipIfIc3IAIsNotAvailable(object):
    """Skip a test if the given solver is not available."""

    def __init__(self):
        pass

    def __call__(self, test_fun):
        msg = "MSatic3 not available"
        skip = False
        try:
            Ic3IA()
        except Ic3IANotAvailable:
            skip = True
        @unittest.skipIf(skip, msg)
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
        skip = self.has_kernel is None or not self.has_kernel
        @unittest.skipIf(skip, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfSOSIsNotAvailable(object):
    """Skip a test if sum of squares is not available."""

    def __init__(self):
        try:
            from SumOfSquares import SOSProblem, poly_opt_prob
            self.has_sos = True
        except ImportError:
            self.has_sos = False

    def __call__(self, test_fun):
        msg = "SoS solver not available"
        skip = not self.has_sos
        @unittest.skipIf(skip, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfPicosIsNotAvailable(object):
    """Skip a test if picos is not available."""

    def __init__(self):
        try:
            import picos
            self.has_picos = True
        except ImportError:
            self.has_picos = False

    def __call__(self, test_fun):
        msg = "SoS solver not available"
        skip = not self.has_picos
        @unittest.skipIf(skip, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper



