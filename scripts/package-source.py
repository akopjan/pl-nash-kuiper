#!/usr/bin/env python3
"""Create the reviewable source archive, excluding caches and proof-export scratch data."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def included(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    if any(part in {'.git', '.lake', '__pycache__'} for part in rel.parts):
        return False
    if rel.parts[:2] == ('verification', 'generated'):
        return False
    return path.is_file() and not path.is_symlink() and path.suffix != '.pyc'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='ZIP path outside the project directory')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error('Choose an output outside the source project to avoid packaging the archive itself')
    output.parent.mkdir(parents=True, exist_ok=True)
    files = sorted(path for path in ROOT.rglob('*') if included(path))
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files:
            archive.write(path, Path('pl_nash_kuiper') / path.relative_to(ROOT))
    with zipfile.ZipFile(output) as archive:
        corrupt = archive.testzip()
        if corrupt is not None:
            raise SystemExit(f'Archive CRC failure: {corrupt}')
    print(f'{output}: {len(files)} files, {output.stat().st_size} bytes')
    print('SHA256:', hashlib.sha256(output.read_bytes()).hexdigest())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
