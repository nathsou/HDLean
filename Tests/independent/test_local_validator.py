"""Kernel and independent replay of the scalable local gate validator."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from independent.replay import replay

LAKE = os.environ.get('LAKE', 'lake')
TOOLS = Path(os.environ.get('HDLEAN_INDEPENDENT_TOOLS', ROOT / 'work/independent-tools/tools.json'))


class LocalValidatorTests(unittest.TestCase):
    def test_kernel_certificates_and_mutations(self):
        module = 'Tests.independent.LocalValidator'
        olean = ROOT / '.lake/build/lib/lean/Tests/independent/LocalValidator.olean'
        olean.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run([LAKE, 'env', 'lean', '-o', olean, '--run',
                                 'Tests/independent/LocalValidator.lean'], cwd=ROOT,
                                text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('PASS: local gate validation', result.stdout)
        if TOOLS.is_file():
            with tempfile.TemporaryDirectory(dir=ROOT / 'work') as tmp:
                report = replay(ROOT, LAKE, TOOLS, tmp,
                                ['HDLean.Backend.Graph.validateLocal_sound',
                                 'HDLean.Tests.LocalValidator.tiny_correct',
                                 'HDLean.Tests.LocalValidator.counter_correct'], [module])
                self.assertTrue(report['passed'])


if __name__ == '__main__':
    unittest.main()
