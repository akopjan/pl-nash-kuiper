#!/usr/bin/env python3
"""Run the pinned Lean against existing local build artifacts, without scheduling Lake jobs."""
import json
import os
from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parents[1]
runtime=Path(subprocess.check_output(
    [str(root/'lakew'), 'env', 'lean', '--print-prefix'], cwd=root, text=True).strip())
manifest=json.loads((root/'lake-manifest.json').read_text())
paths=[root/'.lake/build/lib/lean']
paths += [root/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in manifest['packages']]
env=dict(os.environ)
env['LEAN_PATH']=':'.join(map(str,paths))
os.execve(str(runtime/'bin/lean'),[str(runtime/'bin/lean'),*sys.argv[1:]],env)
