#!/usr/bin/env python3
"""Fail-closed verification with Lean's official kernel.

1. The frozen manifest matches, optionally against an independently approved digest.
2. Frozen spec modules import only frozen modules or Lean itself.
3. `lake build` checks every proof with Lean's kernel; `leanchecker --fresh`
   replays the designs into a fresh kernel environment.
4. Every challenge theorem uses only the standard axioms, and every constant in
   its statement comes from a frozen module, from Lean, or from the manifest's
   implementation holes.
5. The simulation suite passes, and every design is emitted in every format
   through the proved emitter, with the proved parser reading each file back.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from freeze import MANIFEST, frozen_modules, protected_files  # noqa: E402

BASE_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_MODULES = ('Init', 'Std', 'Lean')
DESIGNS = ('fifo', 'counter', 'pipeline', 'ram', 'ring', 'toy16', 'rtl-ram', 'rtl-toy16')
RTL_DESIGNS = ('rtl-ram', 'rtl-toy16')
FORMATS = ('sv', 'aiger', 'rtlil')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(args, log=None):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, text=True, capture_output=True)
    if log:
        log.write_text(result.stdout + result.stderr)
    if result.returncode or 'uncaught exception:' in result.stdout + result.stderr:
        raise RuntimeError(f'command failed ({result.returncode}): {args}\n{result.stdout[-4000:]}\n{result.stderr[-4000:]}')
    return result.stdout


def check_manifest(expected=None, path=MANIFEST):
    if expected and sha(path) != expected:
        raise ValueError('manifest digest differs from the independently approved digest')
    manifest = json.loads(Path(path).read_text())
    if manifest.get('schema') != 2 or not isinstance(manifest.get('files'), dict):
        raise ValueError('unsupported frozen manifest schema')
    required = {str(p.relative_to(ROOT)) for p in protected_files()}
    if set(manifest['files']) != required:
        raise ValueError('frozen manifest omitted or added a protected file')
    for relative, digest in manifest['files'].items():
        file = (ROOT / relative).resolve()
        if not file.is_relative_to(ROOT) or not file.is_file() or sha(file) != digest:
            raise ValueError(f'frozen source mismatch: {relative}')
    return manifest


def check_frozen_imports():
    """A frozen spec must not depend on agent code; only challenges import implementations."""
    frozen = frozen_modules()
    for module in frozen:
        if module.endswith('.Challenge'):
            continue
        source = (ROOT / (module.replace('.', '/') + '.lean')).read_text()
        for imported in re.findall(r'^import\s+(\S+)', source, re.M):
            if imported not in frozen and not imported.startswith(LEAN_MODULES):
                raise ValueError(f'frozen module {module} imports non-frozen {imported}')


def audit(output, holes):
    lines = [s.split('HDLEAN_AUDIT=', 1)[1] for s in output.splitlines() if 'HDLEAN_AUDIT=' in s]
    if len(lines) != 1:
        raise ValueError('missing or ambiguous audit report')
    report = json.loads(lines[0])
    frozen = frozen_modules()
    challenges = [r for r in report if r['module'].endswith('.Challenge')]
    if not challenges:
        raise ValueError('no challenge theorems found')
    for item in report:
        extra = set(item['axioms']) - BASE_AXIOMS
        if extra:
            raise ValueError(f'forbidden axioms in {item["theorem"]}: {sorted(extra)}')
    for item in challenges:
        for constant in item['statement_constants']:
            module = constant['module']
            if module in frozen or module.startswith(LEAN_MODULES) or constant['name'] in holes:
                continue
            raise ValueError(f'{item["theorem"]} mentions {constant["name"]} from non-frozen {module}; '
                             'move it to a frozen interface or list it as an implementation hole')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    parser.add_argument('--manifest-sha256', default=os.environ.get('HDLEAN_TRUSTED_MANIFEST_SHA256') or None)
    parser.add_argument('--backends', action='store_true', help='also run Icarus and Yosys equivalence checks')
    parser.add_argument('--no-clean', action='store_true', help='reuse the build cache')
    parser.add_argument('--report', type=Path, default=ROOT / 'build/signoff.json')
    args = parser.parse_args()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.unlink(missing_ok=True)
    manifest = check_manifest(args.manifest_sha256)
    initial = sha(MANIFEST)
    check_frozen_imports()
    work = ROOT / 'build/verification'
    work.mkdir(parents=True, exist_ok=True)
    if not args.no_clean:
        run([args.lake, 'clean'], work / 'clean.log')
    run([args.lake, 'build', 'HDLean', 'Designs', 'Tests', 'hdlean', 'tests'], work / 'build.log')
    run([args.lake, 'env', 'leanchecker', '--fresh', 'Designs'], work / 'kernel-replay.log')
    report = audit(run([args.lake, 'env', 'lean', 'Tests/Audit.lean'], work / 'audit.log'),
                   set(manifest.get('holes', [])))
    run([ROOT / '.lake/build/bin/tests'], work / 'simulation.log')
    if args.backends:
        run([sys.executable, ROOT / 'scripts/check_backends.py'], work / 'backends.log')
        run([sys.executable, ROOT / 'scripts/check_native_clocks.py', '--lake', args.lake], work / 'native-backends.log')
    artifacts, metrics = {}, {}
    cli = ROOT / '.lake/build/bin/hdlean'
    for design in DESIGNS:
        metrics[design] = json.loads(run([cli, 'metrics', design, '8']))
        for fmt in FORMATS:
            path = work / f'{design}.{fmt}'
            run([cli, 'emit', design, fmt, path, '8'])  # the CLI reads every file back
            artifacts[str(path.relative_to(ROOT))] = sha(path)
    for design in RTL_DESIGNS:
        path = work / f'{design}-words.sv'
        run([cli, 'rtl-emit', design, path])  # word-level text, read back by the proved parser
        artifacts[str(path.relative_to(ROOT))] = sha(path)
    review = work / 'Review.md'
    run([args.lake, 'env', cli, 'review', review])
    if review.read_text() != (ROOT / 'docs/Review.md').read_text():
        raise ValueError('docs/Review.md is stale; regenerate it with `lake env .lake/build/bin/hdlean review docs/Review.md`')
    for fmt in FORMATS:
        path = work / f'async-events.{fmt}'
        run([cli, 'emit-async', fmt, path, '8', '4'])
        artifacts[str(path.relative_to(ROOT))] = sha(path)
    check_manifest(args.manifest_sha256 or initial)
    result = {
        'schema': 2, 'project': 'HDLean', 'status': 'checks-passed',
        'kernel': 'Lean official kernel (lake build, leanchecker --fresh)',
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'spec_approval': manifest['approval'], 'manifest_sha256': sha(MANIFEST),
        'manifest_independently_pinned': bool(args.manifest_sha256),
        'lean': run([args.lake, 'env', 'lean', '--version']).strip(),
        'git_commit': run(['git', 'rev-parse', 'HEAD']).strip(),
        'working_tree_dirty': bool(run(['git', 'status', '--porcelain']).strip()),
        'external_backends': args.backends,
        'theorems': report, 'structural_metrics': metrics, 'artifacts_sha256': artifacts,
        'assumptions': ['Two-flop synchronizers resolve metastability.',
                        'Each output format\'s parser is that format\'s semantics; Yosys and Icarus runs cross-check it.',
                        'Compiled Lean code computes the emitted bytes; the proved parser reads every file back.'],
    }
    args.report.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'PASS: {len(report)} theorems audited; {len(artifacts)} artifacts emitted and read back; {args.report}')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, KeyError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
