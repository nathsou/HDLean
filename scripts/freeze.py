#!/usr/bin/env python3
"""Create a review candidate manifest. This command does not approve specifications."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def protected_files():
    paths = set(ROOT.glob('HDLean/**/*.lean')) | {ROOT / 'HDLean.lean'}
    paths.add(ROOT / 'Verification/Challenge.lean')
    paths.add(ROOT / 'verification/claims.json')
    paths.add(ROOT / 'verification/declarations.json')
    paths.add(ROOT / 'scripts/statement_audit.py')
    paths.update(ROOT.glob('Designs/*/comparator.json'))
    paths.add(ROOT / 'verification/comparator.json')
    paths.add(ROOT / 'verification/branch-protection.json')
    for name in ('Spec.lean', 'Interface.lean', 'Challenge.lean'):
        paths.update(ROOT.glob(f'Designs/*/{name}'))
    # These reference models predate the uniform Spec.lean filename convention.
    paths.update(ROOT / name for name in ('Designs/AsyncFifo/Model.lean',
                                         'Designs/Fifo/Circular.lean'))
    for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Tests/Axioms.lean',
                 'scripts/verify.py', 'scripts/check_backends.py', 'scripts/freeze.py'):
        paths.add(ROOT / name)
    paths.update(ROOT.glob('scripts/independent/*.py'))
    paths.update(ROOT.glob('scripts/comparator/*.py'))
    paths.add(ROOT / 'scripts/independent/pins.json')
    return sorted(paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='replace the candidate manifest')
    args = parser.parse_args()
    manifest = {'schema': 1, 'approval': 'review-required', 'framework': 'HDLean 0.2.0',
                'files': {str(p.relative_to(ROOT)): sha(p) for p in protected_files()}}
    text = json.dumps(manifest, indent=2, sort_keys=True) + '\n'
    if args.write:
        path = ROOT / 'verification/frozen.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        print(f'Candidate manifest SHA-256: {sha(path)}')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
