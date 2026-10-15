#!/usr/bin/env python3
"""Fail-closed development verification, replay, axiom audit, and artifact provenance.

This is an L1 development checker with optional independent nanoda replay.
It does not implement adversarial comparator isolation. L2/L3 are rejected.
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
BASE_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NATIVE_AXIOMS = set()
EXPECTED_THEOREMS = {
    'HDLean.Machine.refines_of_simulation', 'HDLean.refinesAfterReset_of_simulation',
    'HDLean.reset_noninterference', 'HDLean.lowerExpr_correct', 'HDLean.lower_next',
    'HDLean.lower_output', 'HDLean.compose_contracts', 'HDLean.network_refines',
    'HDLean.Backend.Graph.validate_sound',
    'HDLean.Backend.Format.validates_sound', 'HDLean.Backend.Format.correct_of_validated',
    'HDLean.RAMCircuit.hardware_correct', 'HDLean.RAMCircuit.decode_output',
    'HDLean.Circuit.network_correct', 'HDLean.SkidBuffer.Challenge.correctness',
    'HDLean.SkidBuffer.Challenge.budget',
    'HDLean.WordExpr.addWithCarry_correct', 'HDLean.WordExpr.addWithCarry_overflow',
    'HDLean.WordExpr.sub_correct', 'HDLean.WordExpr.ult_correct', 'HDLean.WordExpr.equal_correct',
    'HDLean.WordExpr.signExtend_correct', 'HDLean.WordExpr.setWidth_correct',
    'HDLean.Tests.packet_roundtrip', 'HDLean.Tests.surfaceIncrement_correct',
    'HDLean.SkidBuffer.pipeline_correct', 'HDLean.Netlist.optimize_correct', 'HDLean.retiresLike_of_simulation',
    'HDLean.Fifo.Challenge.correctness', 'HDLean.Fifo.Challenge.budget',
    'HDLean.Fifo.full_rate', 'HDLean.Counter.Challenge.correctness',
    'HDLean.Counter.Challenge.budget', 'HDLean.Toy16.Challenge.correctness',
    'HDLean.sync2_stable', 'HDLean.sample_adjacent', 'HDLean.gray_one_bit8', 'HDLean.one_bit_mix8',
    'HDLean.one_bit_mix', 'HDLean.gray_adjacent', 'HDLean.gray_injective',
    'HDLean.gray_increment_ne', 'HDLean.sample_gray_increment',
    'HDLean.Tests.fifo1_graph', 'HDLean.Tests.counter_graph', 'HDLean.Tests.fifo8_graph',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, log=None):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, text=True, capture_output=True)
    if log:
        log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'command failed ({result.returncode}): {args}\n{result.stdout}\n{result.stderr}')
    # leanchecker 4.34 may print uncaught errors with exit code zero.
    if 'uncaught exception:' in result.stdout or 'uncaught exception:' in result.stderr:
        raise RuntimeError(f'checker raised an exception: {result.stdout}{result.stderr}')
    return result.stdout


def check_manifest(path, expected=None):
    if expected and sha(path) != expected:
        raise ValueError('manifest digest differs from the independently pinned digest')
    manifest = json.loads(path.read_text())
    if manifest.get('schema') != 1 or not isinstance(manifest.get('files'), dict):
        raise ValueError('unsupported frozen manifest schema')
    # The protected file set is part of this trusted checker, not supplied by a submission.
    from freeze import protected_files
    required = {str(p.relative_to(ROOT)) for p in protected_files()}
    if set(manifest['files']) != required:
        raise ValueError('frozen manifest omitted or added a protected file')
    for relative, expected_hash in manifest['files'].items():
        file = (ROOT / relative).resolve()
        if not file.is_relative_to(ROOT) or not file.is_file() or sha(file) != expected_hash:
            raise ValueError(f'frozen source mismatch: {relative}')
    return manifest


def audit_axioms(output, kernel_only=False):
    lines = [s.removeprefix('HDLEAN_AXIOMS=') for s in output.splitlines() if s.startswith('HDLEAN_AXIOMS=')]
    if len(lines) != 1:
        raise ValueError('missing or ambiguous axiom report')
    report = json.loads(lines[0])
    names = [item['theorem'] for item in report]
    if len(names) != len(set(names)) or set(names) != EXPECTED_THEOREMS:
        raise ValueError('axiom report does not contain exactly the required headlines')
    for item in report:
        allowed = BASE_AXIOMS | (set() if kernel_only else NATIVE_AXIOMS)
        unexpected = set(item['axioms']) - allowed
        if unexpected:
            raise ValueError(f'forbidden axioms in {item["theorem"]}: {sorted(unexpected)}')
    return report


def source_snapshot():
    files = sorted(p for folder in ('HDLean', 'Designs', 'Tests') for p in (ROOT / folder).rglob('*.lean'))
    files += [ROOT / p for p in ('HDLean.lean', 'Designs.lean', 'Tests.lean', 'Main.lean', 'lean-toolchain', 'lakefile.toml')]
    return {str(p.relative_to(ROOT)): sha(p) for p in files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--level', choices=['L1', 'L2', 'L3'], default='L1')
    parser.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    parser.add_argument('--manifest-sha256', default=os.environ.get('HDLEAN_TRUSTED_MANIFEST_SHA256'))
    parser.add_argument('--backends', action='store_true', help='require Icarus and Yosys checks')
    parser.add_argument('--independent', action='store_true', help='require independent nanoda replay')
    parser.add_argument('--independent-tools', type=Path, default=ROOT / 'work/independent-tools/tools.json')
    parser.add_argument('--no-clean', action='store_true', help='reuse build cache for local iteration')
    parser.add_argument('--report', type=Path, default=ROOT / 'build/signoff.json')
    args = parser.parse_args()
    if args.level != 'L1':
        parser.error('L2/L3 unavailable: the adversarial comparator sandbox, approved trust surface, '
                     'complete printer proof coverage, and independent nanoda replay are not implemented. '
                     'No sign-off claim has been produced.')
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.unlink(missing_ok=True)
    manifest_path = ROOT / 'verification/frozen.json'
    manifest = check_manifest(manifest_path, args.manifest_sha256)
    before = source_snapshot()
    digest = hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest()
    work = ROOT / 'build/verification' / digest[:16]
    work.mkdir(parents=True, exist_ok=True)
    if not args.no_clean:
        run([args.lake, 'clean'], work / 'clean.log')
    run([args.lake, 'build', 'HDLean', 'Designs', 'Tests', 'hdlean', 'tests'], work / 'build.log')
    run([ROOT / '.lake/build/bin/tests'], work / 'simulation.log')
    if args.backends:
        run([sys.executable, ROOT / 'scripts/check_backends.py'], work / 'backends.log')
    run([args.lake, 'env', 'leanchecker', '--fresh', 'Designs'], work / 'kernel-designs.log')
    run([args.lake, 'env', 'leanchecker', '--fresh', 'Tests'], work / 'kernel-certificates.log')
    axioms = audit_axioms(run([args.lake, 'env', 'lean', 'Tests/Axioms.lean'], work / 'axioms.log'))
    independent_report = None
    if args.independent:
        from independent.replay import replay
        independent_report = replay(ROOT, args.lake, args.independent_tools,
                                    work / 'independent', sorted(EXPECTED_THEOREMS),
                                    ['HDLean', 'Designs', 'Tests'])
    artifacts, metrics = {}, {}
    for design in ('fifo', 'counter', 'pipeline'):
        metrics[design] = json.loads(run([ROOT / '.lake/build/bin/hdlean', 'metrics', design, '8']))
        for fmt in ('sv', 'aiger', 'rtlil'):
            path = work / f'{design}.{fmt}'
            run([ROOT / '.lake/build/bin/hdlean', 'emit', design, fmt, path, '8'])
            artifacts[str(path.relative_to(ROOT))] = sha(path)
    check_manifest(manifest_path, args.manifest_sha256)
    if before != source_snapshot():
        raise ValueError('source files changed during verification')
    report = {
        'schema': 1, 'project': 'HDLean', 'assurance_level': 'L1', 'status': 'development-checks-passed',
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'spec_approval': manifest['approval'], 'manifest_sha256': sha(manifest_path),
        'manifest_independently_pinned': bool(args.manifest_sha256), 'source_digest': digest, 'sources': before,
        'lean': run([args.lake, 'env', 'lean', '--version']).strip(),
        'git_commit': run(['git', 'rev-parse', 'HEAD']).strip(),
        'working_tree_dirty': bool(run(['git', 'status', '--porcelain']).strip()),
        'checks': {'kernel_build': True, 'fresh_kernel_replay': True, 'axiom_policy': True,
                   'simulation': True, 'external_backends': args.backends,
                   'adversarial_comparator': False, 'nanoda': args.independent},
        'independent_replay': independent_report,
        'headline_axioms': axioms, 'structural_metrics': metrics, 'physical_metrics': None,
        'artifacts_sha256': artifacts,
        'assumptions': ['The clock-domain model assumes two-flop synchronizers resolve metastability.'],
        'limitations': [
            'Every emitted graph and final text passes generically proved translation validators for the formalized backend subsets.',
            'Concrete kernel-only graph certificates additionally cover the counter and one/eight-bit two-slot FIFO.',
            'Toy16 is a verified transition-system model and has no synthesizable core backend.',
            'Circular/async FIFO models are tested; their full generic safety/refinement proofs and RTL are pending.',
            'L2/L3, adversarial submission isolation, and physical sign-off remain unavailable.',
        ],
    }
    temporary = args.report.with_suffix('.tmp')
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    temporary.replace(args.report)
    print(f'PASS L1: {args.report}')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, KeyError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
