"""Behavioral tests for the verification boundary, not snapshots of implementation details."""
import copy
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from verify import audit, check_manifest, check_frozen_imports
from waveform import render


class Workflow(unittest.TestCase):
    def report(self, constants=()):
        return [{'theorem': 'HDLean.Counter.Challenge.correctness', 'module': 'Designs.Counter.Challenge',
                 'axioms': ['propext'], 'statement_constants': [
                     {'name': 'HDLean.Counter.Word.wordSpec', 'module': 'Designs.Counter.Interface'},
                     {'name': 'Nat', 'module': 'Init.Prelude'}, *constants]}]

    def test_sorry_and_custom_axioms_rejected(self):
        for axiom in ('sorryAx', 'Submission.claim', 'Fake._native.native_decide.ax_1_6'):
            data = self.report()
            data[0]['axioms'] = [axiom]
            with self.assertRaisesRegex(ValueError, 'forbidden axioms'):
                audit('HDLEAN_AUDIT=' + json.dumps(data), set())

    def test_statement_constant_from_agent_code_rejected(self):
        agent = {'name': 'HDLean.Counter.Word.weakObserve', 'module': 'Designs.Counter.Word'}
        with self.assertRaisesRegex(ValueError, 'non-frozen'):
            audit('HDLEAN_AUDIT=' + json.dumps(self.report([agent])), set())

    def test_declared_hole_accepted(self):
        hole = {'name': 'HDLean.Counter.Word.design', 'module': 'Designs.Counter.Word'}
        audit('HDLEAN_AUDIT=' + json.dumps(self.report([hole])), {'HDLean.Counter.Word.design'})

    def test_fake_report_ambiguity_rejected(self):
        text = 'HDLEAN_AUDIT=' + json.dumps(self.report())
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            audit(text + '\n' + text, set())

    def test_frozen_specs_import_only_frozen_modules(self):
        check_frozen_imports()

    def test_frozen_spec_mismatch_rejected(self):
        manifest = json.loads((ROOT / 'verification/frozen.json').read_text())
        manifest['files']['Designs/Fifo/Spec.lean'] = '0' * 64
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'frozen.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'frozen source mismatch'):
                check_manifest(None, path)

    def test_toy16_observation_map_is_protected(self):
        manifest = json.loads((ROOT / 'verification/frozen.json').read_text())
        self.assertIn('Designs/Toy16/Interface.lean', manifest['files'])
        manifest['files']['Designs/Toy16/Interface.lean'] = '0' * 64
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'frozen.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'frozen source mismatch'):
                check_manifest(None, path)

    def test_weakened_actual_theorem_fails_frozen_statement_check(self):
        lake = os.environ.get('LAKE', 'lake')
        prefix = Path(subprocess.check_output([lake, 'env', 'lean', '--print-prefix'], cwd=ROOT, text=True).strip())
        lean = prefix / 'bin/lean'
        with tempfile.TemporaryDirectory(dir=ROOT / 'work') as tmp:
            tmp = Path(tmp)
            (tmp / 'Designs/Counter').mkdir(parents=True)
            shutil.copytree(ROOT / '.lake/build/lib/lean/Designs', tmp / 'lib/Designs', copy_function=os.symlink)
            for f in (ROOT / '.lake/build/lib/lean').glob('Designs.olean*'):
                (tmp / 'lib' / f.name).symlink_to(f)
            for f in (tmp / 'lib/Designs/Counter').glob('Word.olean*'):
                f.unlink()
            source = (ROOT / 'Designs/Counter/Word.lean').read_text()
            start, end = source.index('theorem correct'), source.index('/-- Four state bits')
            source = source[:start] + 'theorem correct : True := trivial\n\n' + source[end:]
            path = tmp / 'Designs/Counter/Word.lean'
            path.write_text(source)
            env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [tmp / 'lib', ROOT / '.lake/build/lib/lean', prefix / 'lib/lean'])))
            build = subprocess.run([lean, '-R', tmp, '-o', tmp / 'lib/Designs/Counter/Word.olean', path], env=env, capture_output=True, text=True)
            self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
            check = subprocess.run([lean, ROOT / 'Designs/Counter/Challenge.lean'], env=env, capture_output=True, text=True)
            self.assertNotEqual(check.returncode, 0)
            self.assertIn('Type mismatch', check.stdout)
            
            self.assertNotIn('does not exist', check.stdout)

    def test_missing_spec_rejected(self):
        manifest = json.loads((ROOT / 'verification/frozen.json').read_text())
        del manifest['files']['Designs/Fifo/Spec.lean']
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'frozen.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'omitted'):
                check_manifest(None, path)

    def test_external_manifest_digest_rejected(self):
        with self.assertRaisesRegex(ValueError, 'independently approved'):
            check_manifest('0' * 64)

    def test_optimized_python_cannot_disable_backend_checks(self):
        p = subprocess.run([sys.executable, '-O', ROOT / 'scripts/check_backends.py', '--help'],
                           capture_output=True, text=True)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn('requires Python assertions', p.stderr)

    def test_native_parser_rejects_aliases_odd_targets_and_zero_widths(self):
        lake=os.environ.get('LAKE','lake')
        if not shutil.which(lake):
            self.skipTest('Lean is required for native parser checks')
        result=subprocess.run([lake,'env','lean','--run','Tests/BackendProvedMain.lean'],
                              cwd=ROOT,capture_output=True,text=True,timeout=60)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(len(result.stdout.splitlines()),32)

    def test_waveform_cycle_and_little_endian_bits(self):
        rows = [{'cycle': 3, 'inputs': [True, False, True], 'state': [], 'outputs': [False], 'next': []}]
        self.assertIn('3 | 101 | 0 | 0 | 0', render(rows, 'table'))
        self.assertIn('#6\nb101 a', render(rows, 'vcd'))

    def test_width_errors_are_types(self):
        lake = os.environ.get('LAKE', 'lake')
        cases = [
            'open HDLean.Rtl.Build in\ndef illegal (c : Ctx) (a : Sig 4) (b : Sig 8) : M c (Sig 4) := add a b',
            'open HDLean.Rtl.Build in\ndef illegal (c : Ctx) (s : Sig 1) (a : Sig 4) (b : Sig 5) : M c (Sig 4) := mux s a b',
            'open HDLean.Rtl.Build in\ndef illegal (c : Ctx) (s : Sig 2) (a b : Sig 4) : M c (Sig 4) := mux s a b',
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
