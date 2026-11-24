#!/usr/bin/env python3
"""Reproduce the build, source checks, and original-target Lean axiom audit.

Use --comparator for the independent-kernel statement check and --publication
for the identity/licence metadata check. Each command's real exit status and
UTC timestamps are retained in verification/results.json.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='./lakew', help='Lake executable or toolchain wrapper')
    parser.add_argument('--comparator', action='store_true')
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    logs = ROOT / 'verification'
    logs.mkdir(exist_ok=True)
    steps = [
        ('lean-version.txt', [args.lake, 'env', 'lean', '--version']),
        ('source-policy.log', [sys.executable, 'scripts/check-lean-sources.py']),
        ('source-contract.log', [sys.executable, 'scripts/check-contract.py']),
        ('build.log', [args.lake, 'build']),
        ('axioms.log', [args.lake, 'env', 'lean', 'AxiomAudit.lean']),
        ('solution-check.log', [sys.executable, 'scripts/check-solution.py', '--lake', args.lake]),
    ]
    if args.publication:
        steps.append(('publication.log', [sys.executable, 'scripts/check-publication.py']))
    if args.comparator:
        steps.append(('comparator.log', ['bash', 'scripts/verify-comparator.sh']))
    results = []
    for filename, command in steps:
        record = {'command': command, 'started_utc': timestamp(), 'log': filename}
        with (logs / filename).open('w', encoding='utf-8') as output:
            process = subprocess.run(command, cwd=ROOT, text=True, stdout=output,
                                     stderr=subprocess.STDOUT)
        record.update(finished_utc=timestamp(), exit_code=process.returncode)
        results.append(record)
        (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'{filename}: exit {process.returncode}', flush=True)
        if process.returncode:
            print((logs / filename).read_text(), end='')
            return process.returncode
    files = []
    for directory, children, names in os.walk(ROOT):
        children[:] = sorted(d for d in children if d not in
                             {'.git', '.lake', '__pycache__', 'verification'})
        for name in sorted(names):
            path = Path(directory) / name
            if path.is_file() and not path.is_symlink():
                files.append(path)
    manifest = ''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT)}\n'
                       for p in sorted(files))
    (logs / 'sources.sha256').write_text(manifest)
    print('Build and the original theorem dependency audit passed.')
    if not args.comparator:
        print('Comparator is a separate check; use --comparator on a supported Linux host.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
