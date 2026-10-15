"""Fail-closed input checks and exact byte encoding for the certificate generator."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('byte_certificate', ROOT / 'scripts/independent/byte_certificate.py')
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)
AIG = b'aag 1 1 0 1 0\n2\n2\nc\nfixture\n'


class ByteCertificateTests(unittest.TestCase):
    def test_exact_bytes_and_deduplication(self):
        data = b'  repeated\n\tline\r\n  repeated\n\n'
        source, manifest = cert.generate(data, AIG, 'fifo', 8, 'rtlil', 'ByteFixture')
        text = source.decode()
        self.assertEqual(manifest['artifact_sha256'], cert.sha(data))
        self.assertEqual(manifest['artifact_bytes'], len(data))
        self.assertEqual(manifest['source_sha256'], cert.sha(source))
        self.assertIn(':= [byteLine0, byteLine1, byteLine0, byteLine2]', text)
        self.assertIn('List UInt8 := [32, 32, 114, 101, 112, 101, 97, 116, 101, 100]', text)
        self.assertEqual(text.count('private def byteLine'), 3)
        self.assertIn('Format.tokenize_ascii_lines', text)
        self.assertNotIn('native_decide', text)

    def test_reject_unsupported_bytes_and_identifiers(self):
        for data in [b'', b'no final newline', b'\xff\n']:
            with self.assertRaises(ValueError):
                cert.generate(data, AIG, 'counter', 8, 'aiger', 'Fixture')
        for ns in ['bad; axiom x : False', '', 'Fixture..Bad']:
            with self.assertRaises(ValueError):
                cert.generate(AIG, AIG, 'counter', 8, 'aiger', ns)

    def test_reject_malformed_graph(self):
        for graph in [b'aag 1 1 0 0 0\n4\n', b'aag 2 1 1 0 0\n2\n4 2 0\n',
                      b'aag 5 1 0 0 0\n2\n']:
            with self.assertRaises(ValueError):
                cert.graph_from_aiger(graph)


if __name__ == '__main__':
    unittest.main()
