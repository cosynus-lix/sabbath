import os
import errno
import subprocess
import tempfile
import logging
import sys
from shutil import which

def find_exec(exec_name, exec_path = None):
    """Find the executable exec_name on the system (search in system path 
    if exec_path is None)
    """
    if exec_path is None:
        exec_path = which(exec_name)
        if exec_path is None:
            return None
    if not os.path.isfile(exec_path):
        return None

    return exec_path

class VmtResult:
    SAFE = 0
    UNSAFE = 1
    UNKNOWN = 2



class MSatic3NotAvailable(Exception):
    """The msatic3 executable was not found."""
    pass


class MSatic3():
    """
    Wrapper around msatic3
    """


    def __init__(self, msatic3_path=None):
        self.msatic3_path = find_exec("msatic3", msatic3_path)
        if (self.msatic3_path is None or
            not os.path.isfile(self.msatic3_path)):
            raise MSatic3NotAvailable()

    def solve(self, smt2file_path):
        if (not os.path.isfile(smt2file_path)):
            raise FileNotFound(errno.ENOENT, os.strerror(errno.ENOENT),
                               smtfile_path)

        args= [self.msatic3_path,"-m", "ia", "-W", smt2file_path]

        logging.info("Executing %s" % " ".join(args))

        try:
            completed_process = subprocess.run(args,
                                               check = True,
                                               stderr = subprocess.PIPE,
                                               stdout = subprocess.PIPE,
                                               universal_newlines = True)
            assert(completed_process.returncode == 0)
        except subprocess.CalledProcessError as cpe:
            if (cpe.returncode != 1):
                sys.stdout.write(cpe.stdout)
                sys.stderr.write(cpe.stderr)
                sys.stderr.write("%s ended with code %d" % (" ".join(args), cpe.returncode))
                raise cpe
            else:
                completed_process = cpe

        sys.stdout.write(completed_process.stdout)
        sys.stderr.write(completed_process.stderr)
        res = self.parse_out(completed_process.stdout)

        return res

    def parse_out(self, output):
        PRE=0
        STATS=1
        RES=2
        END=3

        res = VmtResult.UNKNOWN

        parse_phase = PRE
        for line in output.splitlines(True):
            line = line.strip()
            if not line: continue

            if parse_phase == PRE:
                if line == "Statistics:":
                    parse_phase = STATS
            elif parse_phase == STATS:
                if line.startswith("mem_used_m"):
                    parse_phase = RES
            elif parse_phase == RES:
                if line == "Safe":
                    res = VmtResult.SAFE
                elif line == "Unsafe":
                    res = VmtResult.UNSAFE
                elif line == "Unknown":
                    res = VmtResult.UNKNOWN

        return res
# EOC Msatic3

def prove_ts(ts, prop):
    res = None

    try:
        (_, tmp_file) = tempfile.mkstemp(suffix=None,
                                         prefix=None,
                                         dir=None,
                                         text=True)
        with open(tmp_file,"w") as outstream:
            ts.to_vmt(outstream, prop)

        print("Verifying %s..." % tmp_file)
        ic3 = MSatic3()
        res = ic3.solve(tmp_file)
    finally:
        if os.path.isfile(tmp_file):
            os.remove(tmp_file)
    return res
