"""End-to-end byte certificates: proof replay and exact artifact binding failures."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from independent import certify_artifact as checker
from independent import byte_certificate

LAKE = os.environ.get('LAKE', 'lake')
TOOLS = Path(os.environ.get('HDLEAN_INDEPENDENT_TOOLS', ROOT / 'work/independent-tools/tools.json'))


@unittest.skipUnless(TOOLS.is_file(), 'build the pinned independent tools before running byte replay tests')
class ByteReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(dir=ROOT / 'work')
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)
        executable = ROOT / '.lake/build/bin/hdlean'
        for fmt in ['aiger', 'sv']:
            subprocess.run([executable, 'emit', 'counter', fmt, self.folder / ('counter.' + fmt)],
                           cwd=ROOT, check=True, capture_output=True)

    def certify(self):
        return checker.certify(ROOT, LAKE, TOOLS, self.folder / 'certificate',
                               self.folder / 'counter.sv', self.folder / 'counter.aiger',
                               'counter', 8, 'sv')

    def test_valid_certificate_and_independent_statement_binding(self):
        report = self.certify()
        self.assertTrue(report['passed'])
        self.assertTrue(report['exact_byte_binding'])
        self.assertEqual(report['roots'], [report['module'] + '.graph_correct', report['module'] + '.text_correct'])
        self.assertEqual(report['independent']['roots'], sorted(report['roots']))
        self.assertEqual(report['artifact_sha256'], checker.sha((self.folder / 'counter.sv').read_bytes()))

    def test_wrong_clock_fails_kernel_and_removes_stale_success(self):
        output = self.folder / 'certificate'
        output.mkdir()
        (output / 'certificate.json').write_text('{"passed": true}')
        artifact = self.folder / 'counter.sv'
        data = artifact.read_bytes()
        self.assertIn(b'posedge clk', data)
        artifact.write_bytes(data.replace(b'posedge clk', b'negedge clk'))
        with self.assertRaisesRegex(RuntimeError, 'kernel byte certificate failed'):
            self.certify()
        self.assertFalse((output / 'certificate.json').exists())

    def test_chunked_lexing_preserves_exact_bytes(self):
        with patch.object(byte_certificate, 'encode_lines',
                          lambda lines: byte_certificate.encode_chunks(lines, size=4)):
            report = self.certify()
        self.assertTrue(report['exact_byte_binding'])

    def test_valid_proof_for_different_bytes_fails_binding(self):
        original = checker.generate
        def wrong_bytes(artifact, *args):
            # Blank lines preserve parsed semantics but are different final bytes.
            return original(b'\n' + artifact, *args)
        with patch.object(checker, 'generate', wrong_bytes):
            with self.assertRaisesRegex(RuntimeError, 'exact artifact bytes'):
                self.certify()
        self.assertFalse((self.folder / 'certificate/certificate.json').exists())


if __name__ == '__main__':
    unittest.main()
