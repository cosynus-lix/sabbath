import sys
import os

# Abstract class
class Result:
    def __init__(self, _):
        raise Exception("Not implemented concrete result")
    def check_consistency_with(self, _):
        raise Exception("Not implemented concrete result")
    def compare(self, _):
        raise Exception("Not implemented concrete result")
    def get_compare_idx(self):
        raise Exception("Not implemented concrete result")
# eof Result

# ---------------------------------------
# Extraction

def check_results(results):
    return all(
        x.check_consistency_with(y)
        for i, x in enumerate(results)
        for j, y in enumerate(results)
        if i != j
    )

def collect_results(res_dir, CResult, extension='log'):
    from glob import glob
    from functools import cmp_to_key
    files = [
        os.path.abspath(y) for x in os.walk(res_dir)
        for y in glob(os.path.join(x[0], f'*.{extension}'))
    ]
    results = [ CResult(os.path.join(res_dir, fname)) for fname in files ]
    results = sorted(results, key=(lambda x : x.get_compare_idx()))
    assert(check_results(results))
    print (f"Processed files: {len(results)}")
    return results

# ---------------------------------------
# Presentation

