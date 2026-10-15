"""Adversarial comparator tests. Namespace integration is mandatory in CI."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from comparator.canonical import compare, digest, read_export
from comparator.compare import (DEFAULT_LIMITS, parse_receipt, run_comparison, safe_child,
                                snapshot, sha, load_tools)
from comparator.sandbox import Sandbox, SandboxUnavailable, limited_run

LAKE = os.environ.get('LAKE', 'lake')
TOOLS = Path(os.environ.get('HDLEAN_INDEPENDENT_TOOLS', ROOT / 'work/independent-tools/tools.json'))


def fixture(folder, optimized=False, wrong_type=False, hidden_axiom=False, native_spoof=False, main=None):
    folder.mkdir(parents=True, exist_ok=True)
    (folder / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
    (folder / 'lakefile.toml').write_text('''name = "comparatorfixture"
[[lean_lib]]
name = "Spec"
[[lean_lib]]
name = "Impl"
[[lean_exe]]
name = "artifact"
root = "Main"
''')
    (folder / 'lake-manifest.json').write_text(json.dumps({'version':'1.2.0','packagesDir':'.lake/packages','packages':[],'name':'comparatorfixture','lakeDir':'.lake','fixedToolchain':False}))
    (folder / 'Spec.lean').write_text('namespace Frozen\ndef target (actual expected : Nat) : Prop := actual = expected\nend Frozen\n')
    impl = '0 + n' if optimized else 'n + 0'
    proof = 'by simp [Frozen.target, implementation]'
    statement = 'Frozen.target (implementation n) n'
    extra = ''
    if wrong_type: statement, proof = 'True', 'True.intro'
    if hidden_axiom: extra, proof = 'axiom hidden : False\n', 'False.elim hidden'
    content = 'module improved(); endmodule\n' if optimized else 'module fixture(); endmodule\n'
    bytes_decl = f'def bytes : String := {json.dumps(content)}'
    if native_spoof:
        bytes_decl = 'def evilBytes : String := "wrong emitted bytes\\n"\n@[implemented_by evilBytes] ' + bytes_decl
    (folder / 'Impl.lean').write_text(f'''import Spec
namespace Block
def implementation (n : Nat) : Nat := {impl}
{extra}theorem correct (n : Nat) : {statement} := {proof}
{bytes_decl}
theorem artifact_correct : bytes.length > 0 := by decide +kernel
end Block
''')
    (folder / 'Main.lean').write_text(main or '''import Impl
def main : IO Unit := do
  IO.FS.createDirAll "build"
  IO.FS.writeFile "build/out.sv" Block.bytes
''')


class ComparatorUnitTests(unittest.TestCase):
    def test_rejects_self_approved_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'receipt.json'
            path.write_text('{"approved": true}')
            with self.assertRaisesRegex(ValueError, 'externally supplied'):
                parse_receipt(path, '0' * 64)
            with self.assertRaisesRegex(ValueError, 'schema'):
                parse_receipt(path, sha(path))

    def test_rejects_artifact_parent_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root / 'redirect').symlink_to('/etc', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'symbolic link'):
                safe_child(root, 'redirect/passwd')
            with self.assertRaises(ValueError): safe_child(root, '../etc/passwd')

    def test_rejects_oversized_source_before_hashing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with (root / 'huge').open('wb') as f: f.truncate(2 * 1048576)
            with self.assertRaisesRegex(ValueError, 'bounds'):
                snapshot(root, limits=dict(DEFAULT_LIMITS, source_mb=1))

    def test_actual_type_and_body_comparison(self):
        reference = {'root': {'kind':'thm', 'type':'approved', 'body':'proof'},
                     'Safe': {'kind':'def', 'type':'Prop', 'body':'strong'},
                     'impl': {'kind':'def', 'type':'Nat', 'body':'old'}}
        candidate = {k:dict(v) for k,v in reference.items()}
        candidate['impl']['body'] = 'new'
        compare(reference, candidate, ['root'], ['Safe','impl'], ['impl'])
        candidate['Safe']['body'] = 'True'
        with self.assertRaisesRegex(ValueError, 'protected declaration'):
            compare(reference,candidate,['root'],['Safe','impl'],['impl'])
        candidate['root']['type'] = 'True'
        with self.assertRaisesRegex(ValueError, 'statement differs'):
            compare(reference,candidate,['root'],['Safe'])

    def test_rejects_ambiguous_export_records(self):
        meta = {'meta':{'format':{'version':'3.1.0'},'lean':{'version':'4.34.0'}}}
        with tempfile.TemporaryDirectory() as tmp:
            export = Path(tmp)/'ambiguous.ndjson'
            export.write_text(json.dumps(meta) + '\n' + '{"ie":0,"sort":0,"bvar":0}\n')
            with self.assertRaisesRegex(ValueError, 'ambiguous expression'):
                read_export(export)
            export.write_text(json.dumps(meta) + '\n' + '{"ie":0,"sort":0,"sort":1}\n')
            with self.assertRaisesRegex(ValueError, 'duplicate JSON'):
                read_export(export)

    def test_mandatory_namespace_flags(self):
        sandbox = Sandbox('/bin/false','/tmp','/bin/true','/bin/true',DEFAULT_LIMITS)
        command = sandbox.command('/tmp',['/bin/true'])
        for flag in ['--unshare-all','--unshare-user','--disable-userns','--cap-drop','--clearenv']:
            self.assertIn(flag, command)
        self.assertNotIn('--share-net',command)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(SandboxUnavailable): sandbox.probe(tmp,Path(tmp)/'probe.log')

    def test_resource_timeout_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(TimeoutError):
                limited_run(['/bin/sleep','10'],Path(tmp)/'timeout.log',dict(DEFAULT_LIMITS,wall_seconds=1))


class ComparatorNamespaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            cls.tools = load_tools(TOOLS)
            cls.toolchain = Path(os.environ.get('HDLEAN_TOOLCHAIN') or subprocess.check_output(
                [LAKE,'env','lean','--print-prefix'],cwd=ROOT,text=True).strip()).resolve()
            cls.bwrap = shutil.which('bwrap')
            if not cls.bwrap: raise SandboxUnavailable('bubblewrap is not installed')
            cls.sandbox = Sandbox(cls.bwrap,cls.toolchain,cls.tools['exporter'],cls.tools['checker'],DEFAULT_LIMITS)
            with tempfile.TemporaryDirectory() as tmp:
                try: cls.sandbox.probe(tmp,Path(tmp)/'probe.log')
                except SandboxUnavailable:
                    reason = (Path(tmp)/'probe.log').read_text()
                    raise SandboxUnavailable(reason)
        except (OSError,ValueError,RuntimeError) as exc:
            if os.environ.get('HDLEAN_REQUIRE_SANDBOX') == '1':
                raise RuntimeError('mandatory CI namespace sandbox unavailable: ' + str(exc)) from exc
            raise unittest.SkipTest('local L2/L3 unavailable: ' + str(exc)) from exc
        cls.toolchain_digest = digest(snapshot(cls.toolchain,filtered=False))

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.reference, self.candidate = self.base/'reference', self.base/'candidate'
        fixture(self.reference); shutil.copytree(self.reference,self.candidate)
        self.output = self.base/'output'
        self.receipt = {'schema':1, 'reference_sha256':digest(snapshot(self.reference)),
                        'toolchain_sha256':self.toolchain_digest,
                        'tools_pins':json.loads(TOOLS.read_text())['pins'],
                        'tool_binaries':{k:sha(v) for k,v in self.tools.items()},
                        'sandbox_sha256':sha(self.bwrap), 'modules':['Impl'],
                        'build_targets':['Spec','Impl','artifact'],
                        'roots':['Block.correct','Block.artifact_correct'],
                        'protected_declarations':['Frozen.target'],
                        'implementation_declarations':['Block.implementation','Block.bytes'],
                        'protected_files':{'Spec.lean':sha(self.reference/'Spec.lean')},
                        'artifacts':[{'path':'build/out.sv','module':'Impl','bytes':'Block.bytes',
                                      'correctness_root':'Block.artifact_correct',
                                      'generate':['/work/.lake/build/bin/artifact']}],
                        'limits':dict(DEFAULT_LIMITS,memory_mb=3072,cpu_seconds=90,wall_seconds=150)}
        self.receipt_path = self.base/'approval.json'
        self.receipt_path.write_text(json.dumps(self.receipt))
        self.approval = sha(self.receipt_path)

    def run_compare(self):
        try:
            return run_comparison(self.reference,self.candidate,self.receipt_path,self.approval,
                                  self.toolchain,TOOLS,self.output,bwrap=self.bwrap)
        except BaseException:
            # Preserve diagnostic evidence in CI's uploaded build directory.
            dest = ROOT/'build/comparator-tests'/self._testMethodName
            if self.output.exists(): shutil.copytree(self.output,dest,dirs_exist_ok=True)
            raise

    def assert_rejected(self, match=None):
        with self.assertRaises((ValueError,RuntimeError)) as exc: self.run_compare()
        if match: self.assertRegex(str(exc.exception),match)
        self.assertFalse((self.output/'acceptance.json').exists())

    def test_accepted_changed_correct_implementation_and_bytes(self):
        fixture(self.candidate,optimized=True)
        report = self.run_compare()
        self.assertTrue(report['nanoda'])
        self.assertIn('Frozen.target',report['protected_declarations'])
        self.assertNotIn('Block.implementation',report['protected_declarations'])
        self.assertIn('build/out.sv',report['artifact_sha256'])
        destination = ROOT/'build/comparator-tests/accepted'
        shutil.copytree(self.output,destination,dirs_exist_ok=True)

    def test_rejects_valid_proof_of_wrong_statement(self):
        fixture(self.candidate,wrong_type=True)
        self.assert_rejected('statement differs')

    def test_rejects_hidden_axiom(self):
        fixture(self.candidate,hidden_axiom=True)
        self.assert_rejected()
        self.assertIn('axiom',(self.output/'candidate-nanoda.log').read_text().lower())

    def test_rejects_changed_protected_source(self):
        (self.candidate/'Spec.lean').write_text('namespace Frozen\ndef target (_ _ : Nat) := True\nend Frozen\n')
        self.assert_rejected('protected source')

    def test_rejects_native_byte_override(self):
        fixture(self.candidate,native_spoof=True)
        self.assert_rejected('sandbox command failed')

    def test_rejects_valid_olean_with_weakened_specification(self):
        spec = 'namespace Frozen\ndef target (_ _ : Nat) : Prop := True\nend Frozen\n'
        impl = '''import Spec
namespace Block
def implementation (n : Nat) : Nat := n + 0
theorem correct (n : Nat) : Frozen.target (implementation n) n := True.intro
def bytes : String := "module fixture(); endmodule\\n"
theorem artifact_correct : bytes.length > 0 := by decide +kernel
end Block
'''
        main = f'''import Impl
def main : IO Unit := do
  IO.FS.writeFile "/tmp/Spec.lean" {json.dumps(spec)}
  IO.FS.writeFile "/tmp/Impl.lean" {json.dumps(impl)}
  for module in ["Spec", "Impl"] do
    let result ← IO.Process.output {{cmd := "/toolchain/bin/lean", args := #["-R", "/tmp", "-o", "/work/.lake/build/lib/lean/" ++ module ++ ".olean", "/tmp/" ++ module ++ ".lean"]}}
    if result.exitCode != 0 then throw (IO.userError (result.stdout ++ result.stderr))
  IO.FS.createDirAll "build"
  IO.FS.writeFile "build/out.sv" Block.bytes
'''
        fixture(self.candidate,main=main)
        self.assert_rejected('protected declaration')

    def test_native_code_cannot_write_specification_or_use_network(self):
        main = '''import Impl
def main : IO Unit := do
  let writable ← try
    IO.FS.writeFile "Spec.lean" "compromised"
    pure true
  catch _ => pure false
  if writable then throw (IO.userError "protected source was writable")
  let network ← IO.Process.output {cmd := "/usr/bin/python3", args := #["-c", "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('1.1.1.1',80)) else 1)"]}
  if network.exitCode != 0 then throw (IO.userError "network escaped")
  IO.FS.createDirAll "build"
  IO.FS.writeFile "build/out.sv" Block.bytes
'''
        fixture(self.candidate,main=main)
        self.assertTrue(self.run_compare()['passed'])


if __name__ == '__main__': unittest.main()
