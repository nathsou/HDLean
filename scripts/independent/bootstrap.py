#!/usr/bin/env python3
"""Locate and pin the proof exporter and independent checkers bundled with Lean.

Since Lean 4.35.0 the toolchain ships `leanexport` and the external kernels
`nanoda`, `con-leche`, `con-ron` and `lean4lean`, plus `leanchecker-paranoid`.
Nothing is downloaded or compiled: this script records the exact binaries of the
project's toolchain and their SHA-256 digests in `work/independent-tools/tools.json`.
`lean4lean` reads `.olean` files rather than exports; `lake check --paranoid` runs it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = json.loads((HERE / 'pins.json').read_text())


def run(command, cwd=None):
    return subprocess.check_output(list(map(str, command)), cwd=cwd, text=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    parser.add_argument('--cache', type=Path, default=ROOT / 'work/independent-tools')
    args = parser.parse_args()
    cache = args.cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    manifest = cache / 'tools.json'
    manifest.unlink(missing_ok=True)
    lean_version = run([args.lake, 'env', 'lean', '--version'], cwd=ROOT).strip()
    if not lean_version.startswith(f'Lean (version {PINS["lean"]},'):
        raise ValueError(f'expected Lean {PINS["lean"]}; got {lean_version}')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + PINS['lean']:
        raise ValueError('lean-toolchain and pinned Lean version differ')
    bindir = Path(run([args.lake, 'env', 'lean', '--print-prefix'], cwd=ROOT).strip()) / 'bin'
    names = {'exporter': PINS['exporter'], 'checker': PINS['checker'],
             **{name: name for name in PINS['extra_checkers']}}
    binaries = {}
    for key, name in names.items():
        path = (bindir / name).resolve(strict=True)
        binaries[key] = {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    report = {'schema': 2, 'pins': PINS, 'lean_version': lean_version, 'binaries': binaries}
    manifest.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Pinned bundled tools: {manifest}')


if __name__ == '__main__':
    main()
