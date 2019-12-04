import os
import subprocess
import StringIO
import string
import logging

from barrier.printers import QepcadPrinter


class QepcadDriver():
    """
    Call qepcad via pipe.

    In the future: the driver should become a solver in PySMT.
    """

    QEPCAD_INPUT_TEMPLATE = """
[Case]
${VARS}
${FREE_VARS_NUMBER}
${QEFORMULA}
finish.
"""

    @staticmethod
    def call_qepcad(formula, free_var, not_free):
        """
        """
        def variables_qepcad_format(list_var):
            str_var = "("
            for i in range(len(list_var)-1):
                str_var = str_var+str(list_var[i])+","
            str_var = str_var+str(list_var[-1])+")"
            return str_var

        logger = logging.getLogger(__name__)

        # Creates the input stream to pass as input to qepcad
        #
        # Prints (example):
        # [Case]
        # (p1,p2,p3,x1,x2)
        # 3
        # [ p1 x1 > 0 /\ p2 x2 = 0]
        #
        #ordering the variables for qepcad as (free_var,not_free)
        ordered_var_list = list(free_var) + list(not_free)
        formula_stream = StringIO.StringIO()
        res = QepcadPrinter(formula_stream)
        res.printer(formula)
        substitutions = {"VARS" : variables_qepcad_format(ordered_var_list),
                         "FREE_VARS_NUMBER" : len(free_var),
                         "QEFORMULA" : formula_stream.getvalue()}
        qepcad_input = string.Template(QepcadDriver.QEPCAD_INPUT_TEMPLATE).safe_substitute(substitutions)

        # Command line to execute qepcad - require to have $qe set in the global PATH.
        #
        # $> $qe/bin/qepcad +N8000000
        #
        # Using qepcad_input as input.
        if 'qe' not in os.environ:
            raise Exception("qe environment variable not set!")

        qepath = os.path.join(os.environ['qe'], "bin", "qepcad")
        if not os.path.isfile(qepath):
            raise Exception("Path to qe (%s) not found!" % qepath)
        args = [qepath, "+N8000000"]

        logger.debug("Calling: %s\nWith input: %s" % (" ".join(args), qepcad_input))
        p = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
        qepcad_output, err = p.communicate(input=qepcad_input)

        logger.debug("Qepcad computation ended with return code %d" % p.returncode)

        if p.returncode != 0:
            logger.debug("Error calling qepcad.\nstderr is:\n %s\n" % (stderr))
            raise Exception("qepcad returned with error code %d" % p.returncode)

        # Parse the qepcad output
    
        print(qepcad_output)
