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

    def test_large_artifacts_stage_automatically(self):
        modules, manifest = cert.generate_modules(b'line\n' * 8193, AIG, 'counter', 8, 'aiger', 'Fixture')
        self.assertEqual(manifest['module_order'], list(modules))
        self.assertIn('Fixture_Lexer4', modules)
        self.assertEqual(manifest['source_sha256'], cert.sha(modules['Fixture']))
        self.assertNotIn('rawChunk0 :', modules['Fixture'].decode())
        self.assertIn('import Fixture_Graph', modules['Fixture'].decode())
        self.assertIn('Graph.validateLocal_sound', modules['Fixture_Graph'].decode())
        with self.assertRaises(ValueError):
            cert.generate_modules(AIG, AIG, 'counter', 8, 'aiger', 'Fixture', chunks_per_module=0)

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

    def test_extended_designs_and_bounded_graph_literals(self):
        for design, expected in [('pipeline', 'SkidBuffer.hardware 8'),
                                 ('ram', 'RAMCircuit.hardware 4 8'),
                                 ('toy16', 'Toy16.Physical.hardware Toy16.sumProgram'),
                                 ('ring', 'Fifo.Circular.Physical.hardware 4 8')]:
            source, manifest = cert.generate(AIG, AIG, design, 8, 'aiger', 'Fixture')
            self.assertIn(expected, source.decode())
            self.assertEqual(manifest['design'], design)
            self.assertIn('Graph.validateLocal_sound', source.decode())
        self.assertIn('List.flatten', cert.array(range(300)))


if __name__ == '__main__':
    unittest.main()
