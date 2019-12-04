import os
import subprocess
import StringIO
import string
import logging
import re

from pysmt.shortcuts import TRUE

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
        Call qepcad on formula, assuming free_var is a list of free variables in
        formula and not_free is a list of non free variables in the formula.

        Returns the formula obtained after calling qepcad.

        The environment variable $qe must be set in the system as described in the
        installation of qepcad.
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
        pysmt_result = QepcadDriver.parse_qepcad_output(qepcad_output)

        logger.debug("Qepcad computation result: %s" % str(pysmt_result))

        return pysmt_result

    @staticmethod
    def parse_qepcad_output(qepcad_output):
        """
        Parses the whole output generated from qepcad and parses the equivalent
        quantifier-free formula as a PySMT formula.

        qepcad_output is a string containing the output from qepcad.
        """
        logger = logging.getLogger(__name__)

        # 1. Get the returned formula - use re to locate the formula string.
        pattern = re.compile(r'.+An equivalent quantifier-free formula:(.+)=====================  The End  =====================.+',
                             re.M|re.DOTALL)

        matched = pattern.match(qepcad_output)

        if (not matched):
            logger.error("Malformed output from qepcad.\n%s" % qepcad_output)
            raise Exception("Malformed output from qepcad")
        else:
            qepcad_formula = matched.group(1)
            qepcad_formula = qepcad_formula.strip()

            logger.debug("Qepcad formula: %s" % qepcad_formula)

            # 2. Parses the qepcad formula
            pysmt_formula = TRUE

        return TRUE
