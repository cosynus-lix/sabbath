""" Generates the benchmarks with a specified set of predicates.

The tool extracts 4 sets of predicates, as in the in the VMCAI 2016 paper:
  - factors of the RHS of the ODEs and of the safety property (called "factors")
  - factors and (first) lie derivatives
  - factors and algebraic invariants
  - factors, lie derivatives, algebraic invariants

"""

import sys
import argparse
import os

from pysmt.shortcuts import get_env

from barrier.lzz.serialization import importInvar, serializeInvar
from barrier.decomposition.predicates import AbsPredsTypes, get_predicates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input",help="Input folder")
    parser.add_argument("--output",help="Output folder")
    parser.add_argument("--predtypes",
                        choices=["factors",
                                 "factors_lie",
                                 "factors_invar",
                                 "factors_lie_invar"],
                        default="factors",
                        help="Selects the predicates for the abstraction")

    args = parser.parse_args()
    for path in [args.input, args.output]:
        if path is None:
            sys.stderr.write("Missing path!\n")
            sys.exit(1)
        else:
            path = os.path.abspath(path)
            if not os.path.isdir(path):
                sys.stderr.write("Missing path %s!\n" % path)
                sys.exit(1)

    if args.predtypes == "factors":
        abs_type = 0 | AbsPredsTypes.FACTORS.value
    elif args.predtypes == "factors_lie":
        abs_type = (AbsPredsTypes.FACTORS.value |
                    AbsPredsTypes.LIE.value)
    elif args.predtypes == "factors_invar":
        abs_type = (AbsPredsTypes.FACTORS.value |
                    AbsPredsTypes.INVAR.value)
    elif args.predtypes == "factors_lie_invar":
        abs_type = (AbsPredsTypes.FACTORS.value |
                    AbsPredsTypes.LIE.value |
                    AbsPredsTypes.INVAR.value)
    else:
        raise Exception("Unkonwn preds type!")

    env = get_env()
    input_path = os.path.abspath(args.input)
    output_path = os.path.abspath(args.output)
    for invar_file in os.listdir(input_path):
        if (not invar_file.endswith(".invar")):
            continue

        with open(os.path.join(input_path, invar_file), "r") as json_stream:
            problem_list = importInvar(json_stream, env)

            new_problem_list = []
            for problem in problem_list:
                (problem_name, ant, cons, dyn_sys, invar, predicates) = problem

                print("Extracting the predicates for %s" % problem_name)

                new_predicates = get_predicates(problem, abs_type)

                new_problem = (problem_name, ant, cons, dyn_sys, invar,
                               new_predicates)
                new_problem_list.append(new_problem)

            new_invar_file = "%s_%s.invar" % (invar_file[:-len(".invar")],
                                              args.predtypes)
            out_file_name = os.path.join(output_path, new_invar_file)
            with open(out_file_name, "w") as outstream:
                serializeInvar(outstream, new_problem_list, env)

if __name__ == '__main__':
    main()
