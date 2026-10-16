#!/usr/bin/env python3
"""Create a review candidate manifest. This command does not approve specifications.

The manifest pins every reviewer-owned and framework file by SHA-256 and lists the
implementation holes: agent-defined constants that challenge statements may name
(the hardware itself and facts about its type). Everything else a challenge
statement mentions must come from a frozen module or from Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'verification/frozen.json'

# Reviewer-owned files whose names predate the Spec/Interface/Challenge convention.
EXTRA_FROZEN = ('Designs/AsyncFifo/Model.lean', 'Designs/Fifo/Circular.lean')
TOOLING = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Tests/Audit.lean',
           'scripts/verify.py', 'scripts/freeze.py', 'scripts/check_backends.py',
           'scripts/check_native_clocks.py', 'verification/branch-protection.json')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def protected_files():
    paths = set(ROOT.glob('HDLean/**/*.lean')) | {ROOT / 'HDLean.lean'}
    for name in ('Spec.lean', 'Interface.lean', 'Challenge.lean'):
        paths.update(ROOT.glob(f'Designs/*/{name}'))
    paths.update(ROOT / name for name in EXTRA_FROZEN + TOOLING)
    return sorted(paths)


def frozen_modules():
    """Lean module names of the frozen .lean files."""
    return {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.')
            for p in protected_files() if p.suffix == '.lean' and not p.name == 'Audit.lean'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='replace the candidate manifest')
    args = parser.parse_args()
    holes = json.loads(MANIFEST.read_text()).get('holes', []) if MANIFEST.exists() else []
    manifest = {'schema': 2, 'approval': 'review-required', 'framework': 'HDLean 0.3.0',
                'holes': sorted(holes),
                'files': {str(p.relative_to(ROOT)): sha(p) for p in protected_files()}}
    text = json.dumps(manifest, indent=2, sort_keys=True) + '\n'
    if args.write:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(text)
        print(f'Candidate manifest SHA-256: {sha(MANIFEST)}')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
