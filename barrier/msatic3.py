import os
import errno
import subprocess
import tempfile
import logging
import sys
from shutil import which

class MSatic3NotAvailable(Exception):
    """The msatic3 executable was not found."""
    pass

class MSatic3():
    """
    Wrapper around msatic3
    """

    class Result:
        SAFE = 0
        UNSAFE = 1
        UNKNOWN = 2

    def find_msatic(msatic3_path = None):
        if msatic3_path is None:
            msatic3_path = which("msatic3")
            if msatic3_path is None:
                return None
        if not os.path.isfile(msatic3_path):
            return None

        return msatic3_path

    def __init__(self, msatic3_path=None):
        self.msatic3_path = MSatic3.find_msatic(msatic3_path)
        if (self.msatic3_path is None):
            raise MSatic3NotAvailable()

        if msatic3_path is None:
            self.msatic3_path = which("msatic3")
            if self.msatic3_path is None:
                raise MSatic3NotAvailable()
        else:
            self.msatic3_path = msatic3_path

        if not os.path.isfile(self.msatic3_path):
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

        res = MSatic3.Result.UNKNOWN

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
                    res = MSatic3.Result.SAFE
                elif line == "Unsafe":
                    res = MSatic3.Result.UNSAFE
                elif line == "Unknown":
                    res = MSatic3.Result.UNKNOWN

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
