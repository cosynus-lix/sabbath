import sys
import argparse
import logging
import os
import signal
import sys
import re


re_str = "[~]*[0-9]+{[a-zA-Z0-9\_\(\)<=>*+-/-\s]+}"
atom_re = re.compile(re_str)
readable_re = re.compile("[0-9]+{([a-zA-Z0-9\_\(\)<=>*+-/-\s]+)}")

trace = []
with open("/tmp/trace.txt", "r") as f:
    for line in f.readlines():
        line = line.strip()
        to_replace = ["[","]"]
        for r in to_replace:
            line = line.replace(r,"")


        trace_val = {}
        for match in atom_re.finditer(line):
            atom = match.group(0)

            if not atom:
                continue

            val = True
            if (atom[0] == "~"):
                val = False
                atom = atom[1:]
            trace_val[atom] = val
        trace.append(trace_val)



def print_trace(trace):
    for (atom,value) in trace.items():
        name = readable_re.match(atom)

        if (value):
            sys.stdout.write("%s " % name.group(1))
        else:
            sys.stdout.write("~%s " % name.group(1))
    sys.stdout.write("\n")

index = 0
prev_state = None
for t in trace:
    if index == 0:
        print_trace(trace[index])
    else:
        changed = {}

        prev_trace = trace[index - 1]
        for (atom, value) in trace[index].items():
            if prev_trace[atom] != value:
                changed[atom] = value

        print_trace(changed)

    index = index + 1
