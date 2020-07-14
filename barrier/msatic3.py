import os
import errno
import subprocess
from shutil import which
from pysmt.exceptions import SolverAPINotFound

class MSatic3():
    """
    Wrapper around msatic3
    """

    class Result:
        SAFE = 0
        UNSAFE = 1
        UNKNOWN = 2

    def __init__(self, msatic3_path=None):
        if msatic3_path is None:
            self.msatic3_path = which("msatic3")
            if self.msatic3_path is None:
                raise SolverAPINotFound()
        else:
            self.msatic3_path = msatic3_path

        if not os.path.isfile(self.msatic3_path):
            raise SolverAPINotFound()


    def solve(self, smt2file_path):
        if (not os.path.isfile(smt2file_path)):
            raise FileNotFound(errno.ENOENT, os.strerror(errno.ENOENT),
                               smtfile_path)

        args= [self.msatic3_path,"-m", "ia", "-W", smt2file_path]

        p = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
        output, err = p.communicate()

        res = self.parse_out(output)
        return res

    def parse_out(self, output):
        PRE=0
        STATS=1
        RES=2
        END=3

        res = MSatic3.Result.UNKNOWN

        parse_phase = PRE
        for line in output.splitlines(True):
            line = line.strip()
            if not line: continue

            if parse_phase == PRE:
                if line == b"Statistics:":
                    parse_phase = STATS
            elif parse_phase == STATS:
                if line.startswith(b"mem_used_mb"):
                    parse_phase = RES
            elif parse_phase == RES:
                if line == b"Safe":
                    res = MSatic3.Result.SAFE
                elif line == b"Unsafe":
                    res = MSatic3.Result.UNSAFE
                elif line == b"Unknown":
                    res = MSatic3.Result.UNKNOWN

        return res
