"""Behavioral tests for the verification boundary, not snapshots of implementation details."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from verify import audit_axioms, check_manifest, EXPECTED_THEOREMS
from waveform import render


class Workflow(unittest.TestCase):
    def report(self):
        return [{'theorem': name, 'axioms': []} for name in sorted(EXPECTED_THEOREMS)]

    def test_sorry_and_custom_axioms_rejected(self):
        for axiom in ('sorryAx', 'Submission.claim', 'Fake._native.bv_decide.ax_1_6'):
            data = self.report()
            data[0]['axioms'] = [axiom]
            with self.assertRaisesRegex(ValueError, 'forbidden axioms'):
                audit_axioms('HDLEAN_AXIOMS=' + json.dumps(data))

    def test_missing_or_duplicated_headline_rejected(self):
        for data in (self.report()[:-1], self.report() + self.report()[:1]):
            with self.assertRaisesRegex(ValueError, 'exactly the required'):
                audit_axioms('HDLEAN_AXIOMS=' + json.dumps(data))

    def test_fake_report_ambiguity_rejected(self):
        text = 'HDLEAN_AXIOMS=' + json.dumps(self.report())
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            audit_axioms(text + '\n' + text)

    def test_frozen_spec_mismatch_rejected(self):
        manifest = json.loads((ROOT / 'verification/frozen.json').read_text())
        manifest['files']['Designs/Fifo/Spec.lean'] = '0' * 64
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'frozen.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'frozen source mismatch'):
                check_manifest(path)

    def test_missing_spec_rejected(self):
        manifest = json.loads((ROOT / 'verification/frozen.json').read_text())
        del manifest['files']['Designs/Fifo/Spec.lean']
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'frozen.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'omitted'):
                check_manifest(path)

    def test_external_manifest_digest_rejected(self):
        with self.assertRaisesRegex(ValueError, 'independently pinned'):
            check_manifest(ROOT / 'verification/frozen.json', '0' * 64)

    def test_assurance_level_does_not_silently_downgrade(self):
        for level in ('L2', 'L3'):
            p = subprocess.run([sys.executable, ROOT / 'scripts/verify.py', '--level', level], capture_output=True, text=True)
            self.assertNotEqual(p.returncode, 0)
            self.assertIn('unavailable', p.stderr)

    def test_optimized_python_cannot_disable_backend_checks(self):
        p = subprocess.run([sys.executable, '-O', ROOT / 'scripts/check_backends.py', '--help'],
                           capture_output=True, text=True)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn('requires Python assertions', p.stderr)

    def test_waveform_cycle_and_little_endian_bits(self):
        rows = [{'cycle': 3, 'inputs': [True, False, True], 'state': [], 'outputs': [False], 'next': []}]
        self.assertIn('3 | 101 | 0 | 0 | 0', render(rows, 'table'))
        self.assertIn('#6\nb101 a', render(rows, 'vcd'))

    def test_clock_domain_and_width_errors_are_types(self):
        lake = os.environ.get('LAKE', 'lake')
        cases = [
            'def illegal : HDLean.Expr 1 1 1 := (HDLean.Expr.input 0 : HDLean.Expr 0 1 1)',
            'def illegal : HDLean.WordExpr 0 1 1 4 := HDLean.WordExpr.literal (3 : BitVec 8)',
            'def illegal : HDLean.Expr 0 1 1 := .reg ⟨2, by decide⟩',
        ]
        with tempfile.TemporaryDirectory(dir=ROOT / 'work') as tmp:
            for n, source in enumerate(cases):
                path = Path(tmp) / f'Negative{n}.lean'
                path.write_text('import HDLean\n' + source + '\n')
                p = subprocess.run([lake, 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(p.returncode, 0, source)
                self.assertIn('error', p.stdout)


if __name__ == '__main__':
    (ROOT / 'work').mkdir(exist_ok=True)
    unittest.main()
