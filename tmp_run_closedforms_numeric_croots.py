import os
import runpy
import sys

ROOT = "/home/mtm20cb/tools/freqhorn/tools/polar"
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import settings
settings.numeric_roots = False
settings.numeric_croots = True
settings.numeric_eps = 1e-8

sys.argv = ["closedforms2.py", "/home/mtm20cb/tools/freqhorn/out.prob", "_fh_5"]
runpy.run_path("/home/mtm20cb/tools/freqhorn/tools/polar/closedforms2.py", run_name="__main__")
