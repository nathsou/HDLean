#!/usr/bin/env python3
"""Build the pinned, unmodified proof exporter and independent Rust checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = json.loads((HERE / 'pins.json').read_text())


def run(command, cwd=None, env=None):
    print('+', ' '.join(map(str, command)), flush=True)
    return subprocess.check_output(list(map(str, command)), cwd=cwd, env=env, text=True)


def checkout(path, pin):
    if not path.exists():
        path.mkdir(parents=True)
        run(['git', 'init', path])
        run(['git', '-C', path, 'remote', 'add', 'origin', pin['url']])
    if run(['git', '-C', path, 'remote', 'get-url', 'origin']).strip() != pin['url']:
        raise ValueError(f'unexpected origin: {path}')
    if run(['git', '-C', path, 'status', '--porcelain', '--untracked-files=no']).strip():
        raise ValueError(f'refusing modified source tree: {path}')
    run(['git', '-C', path, 'fetch', '--depth', '1', 'origin', pin['commit']])
    run(['git', '-C', path, 'checkout', '--detach', pin['commit']])
    if run(['git', '-C', path, 'rev-parse', 'HEAD']).strip() != pin['commit']:
        raise ValueError(f'wrong source revision: {path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    parser.add_argument('--cargo', default=os.environ.get('CARGO', 'cargo'))
    parser.add_argument('--cache', type=Path, default=ROOT / 'work/independent-tools')
    args = parser.parse_args()
    cache = args.cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    manifest = cache / 'tools.json'
    manifest.unlink(missing_ok=True)
    lean_version = run([args.lake, 'env', 'lean', '--version'], cwd=ROOT).strip()
    if not lean_version.startswith(f'Lean (version {PINS["lean"]},'):
        raise ValueError(f'expected Lean {PINS["lean"]}; got {lean_version}')
    # cargo +version works through rustup; never silently select another compiler.
    cargo = [args.cargo, '+' + PINS['rust']]
    rust_version = run([*cargo, '--version']).strip()
    if not rust_version.startswith('cargo ' + PINS['rust'] + ' '):
        raise ValueError(f'wrong Rust toolchain: {rust_version}')
    exporter, checker = cache / 'lean4export', cache / 'nanoda'
    checkout(exporter, PINS['lean4export'])
    checkout(checker, PINS['nanoda'])
    if (exporter / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + PINS['lean']:
        raise ValueError('exporter and project Lean versions differ')
    print(run([args.lake, 'build'], cwd=exporter), end='')
    # Bound build concurrency while other project checks run.
    print(run([*cargo, 'build', '--locked', '--release', '--jobs', '2'], cwd=checker), end='')
    binaries = {'exporter': exporter / '.lake/build/bin/lean4export',
                'checker': checker / 'target/release/nanoda_bin'}
    report = {'schema': 1, 'pins': PINS, 'lean_version': lean_version,
              'cargo_version': rust_version, 'binaries': {
                  key: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                  for key, path in binaries.items()}}
    manifest.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Built pinned tools: {manifest}')


if __name__ == '__main__':
    main()
