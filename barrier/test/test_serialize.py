"""
WARNING: Test cases calls the LMI solver, which is somehow non-deterministic (maybe there is a seed to set). So, some tests may fail depending on the LMI result (still did not happened)

"""
import io 
import json



from pysmt.typing import REAL
from pysmt.shortcuts import *

from barrier.system import DynSystem

from serialization import serializeSynthesis, importSynthesis

from . import TestCase

class TestSerialize(TestCase):
    def test_write_read(self):
        env = get_env()

        x,y,z = [Symbol("x%s" % (i+1), REAL) for i in range(3)]
        sys = DynSystem([x,y,z], [], [],
                        {x : x * Real(-1) + Real(1),
                         y : z + x + y * Real(-2) + Real(2),
                         z : z + x + y * Real(-2) + Real(2)},
                        {})
        systems = [sys,sys]
        Theta_smt = Real(0)
        refvalues_smt = [Real(1),Real(2),Real(3)]
        lyap = [x + y, y + z]
        assumptions = Equals(x,y)

        f = io.StringIO()
        serializeSynthesis(f,
                           systems,
                           Theta_smt,
                           refvalues_smt,
                           Real(0) if lyap is None else lyap[0],
                           Real(0) if lyap is None else lyap[1],
                           assumptions,
                           env)
        f.seek(0)

        json_data = json.load(f)
        (sys2, theta2, ref2, lp0, lp1, ass2) = importSynthesis(json_data,env)

        self.assertTrue(theta2 == Theta_smt)
        self.assertTrue(lyap[0] == lp0)
        self.assertTrue(lyap[1] == lp1)
        self.assertTrue(ass2 == assumptions)
