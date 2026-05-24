import os
import sys
import time

ROOT = "/home/mtm20cb/tools/freqhorn/tools/polar"
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import settings
from inputparser import Parser
from program import normalize_program
from recurrences import RecBuilder
from recurrences.solver import RecurrenceSolver

settings.numeric_roots = False
settings.numeric_croots = True
settings.numeric_eps = 1e-8

program = Parser().parse_file("/home/mtm20cb/tools/freqhorn/out.prob")
program = normalize_program(program)
rec_builder = RecBuilder(program)
recurr = rec_builder.get_recurrences("_fh_5")

start = time.time()
closed_form = RecurrenceSolver(recurr).get("_fh_5")
elapsed = time.time() - start
print(f"elapsed={elapsed:.3f}s")
print(type(closed_form).__name__)
print(str(closed_form)[:1000])
