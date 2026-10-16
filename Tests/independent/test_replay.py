"""Policy regressions and real nanoda rejection tests (never mock the checker)."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('independent_replay', ROOT / 'scripts/independent/replay.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lake = os.environ.get('LAKE', 'lake')
        cls.manifest = Path(os.environ.get('HDLEAN_INDEPENDENT_TOOLS',
                                          ROOT / 'work/independent-tools/tools.json'))
        if not cls.manifest.exists():
            raise unittest.SkipTest('run scripts/independent/bootstrap.py before integration tests')
        cls.tools = replay.load_tools(cls.manifest)
        (ROOT / 'work').mkdir(exist_ok=True)
        cls.tmp = tempfile.TemporaryDirectory(prefix='independent-test-', dir=ROOT / 'work')
        cls.project = Path(cls.tmp.name)
        (cls.project / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
        (cls.project / 'lakefile.toml').write_text(
            'name = "independent_tests"\n[[lean_lib]]\nname = "Fixtures"\n')
        shutil.copy(Path(__file__).with_name('Fixtures.lean'), cls.project / 'Fixtures.lean')
        subprocess.run([cls.lake, 'build', 'Fixtures'], cwd=cls.project,
                       check=True, capture_output=True, text=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def export(self, theorem, suffix):
        path = self.project / (suffix + '.ndjson')
        with path.open('w') as stream:
            subprocess.run([self.lake, 'env', str(self.tools['exporter']), 'Fixtures', '--', *([theorem] if isinstance(theorem,str) else theorem)],
                           cwd=self.project, stdout=stream, check=True, timeout=60)
        return path

    def raw_checker(self, export):
        config = export.with_suffix('.json')
        config.write_text(json.dumps(replay.checker_config(export)))
        return subprocess.run([str(self.tools['checker']), str(config)], cwd=self.project,
                              capture_output=True, text=True, timeout=60)

    def test_valid_proof_replays(self):
        result = replay.replay(self.project, self.lake, self.manifest, self.project / 'valid',
                               ['IndependentFixtures.valid'], ['Fixtures'], timeout=60)
        self.assertTrue(result['passed'])
        self.assertGreater(result['checked_declarations'], 0)

    def test_foreign_sorry_and_native_axioms_rejected_by_both_layers(self):
        for name in ('foreignProof', 'admitted', 'nativeProof'):
            with self.subTest(name=name):
                root = 'IndependentFixtures.' + name
                path = self.export(root, name)
                with self.assertRaisesRegex(ValueError, 'forbidden axiom'):
                    replay.audit_export(path, [root])
                self.assertNotEqual(self.raw_checker(path).returncode, 0)

    def test_corrupted_proof_rejected_by_nanoda(self):
        path = self.export('IndependentFixtures.valid', 'tampered')
        records = [json.loads(line) for line in path.read_text().splitlines()]
        wrong_value = next(item['ie'] for item in records if 'sort' in item)
        records[-1]['thm']['value'] = wrong_value
        path.write_text(''.join(json.dumps(item) + '\n' for item in records))
        replay.audit_export(path, ['IndependentFixtures.valid'])
        self.assertNotEqual(self.raw_checker(path).returncode, 0)

    def test_missing_roots_fail_and_stale_success_is_removed(self):
        path = self.export('IndependentFixtures.valid', 'missing')
        with self.assertRaisesRegex(ValueError, 'missing'):
            replay.audit_export(path, ['IndependentFixtures.absent'])
        output = self.project / 'stale'
        output.mkdir()
        report = output / 'replay.json'
        report.write_text('{"passed": true}')
        with self.assertRaises((ValueError, RuntimeError)):
            replay.replay(self.project, self.lake, self.manifest, output,
                          ['IndependentFixtures.foreignProof'], ['Fixtures'])
        self.assertFalse(report.exists())

    def test_empty_and_duplicate_root_sets_fail(self):
        path = self.export('IndependentFixtures.valid', 'roots')
        for roots in ([], ['IndependentFixtures.valid'] * 2):
            with self.assertRaises(ValueError):
                replay.audit_export(path, roots)

    def run_serial_adapter(self, export, reject_unused):
        template = (ROOT / 'scripts/independent/nanoda_serial.py').read_text()
        body = template.replace('@HDLEAN_CHECKER@',str(self.tools['checker'])).replace(
            '@HDLEAN_CHECKER_SHA256@',replay.sha(self.tools['checker']))
        if not reject_unused:
            body = body.replace('REJECT_UNUSED_AXIOMS = True','REJECT_UNUSED_AXIOMS = False')
        adapter = self.project / ('serial-strict.py' if reject_unused else 'serial-whole.py')
        adapter.write_text(body)
        config = export.with_suffix('.adapter.json')
        config.write_text(json.dumps(replay.checker_config(export)))
        return subprocess.run(['python3',str(adapter),str(config)],capture_output=True,text=True,timeout=60)

    def test_whole_project_policy_omits_unused_axioms_but_rejects_every_use(self):
        unused = self.export(['IndependentFixtures.valid','IndependentFixtures.foreign'],'unused-axiom')
        accepted = self.run_serial_adapter(unused,reject_unused=False)
        self.assertEqual(accepted.returncode,0,accepted.stdout+accepted.stderr)
        self.assertIn('skipping exported but unpermitted axioms',accepted.stdout)
        self.assertNotEqual(self.run_serial_adapter(unused,reject_unused=True).returncode,0)
        used = self.export('IndependentFixtures.foreignProof','used-axiom')
        self.assertNotEqual(self.run_serial_adapter(used,reject_unused=False).returncode,0)

    def test_modified_binary_digest_fails(self):
        data = json.loads(self.manifest.read_text())
        data['binaries']['checker']['sha256'] = '0' * 64
        path = self.project / 'bad-tools.json'
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            replay.load_tools(path)


if __name__ == '__main__':
    unittest.main()
