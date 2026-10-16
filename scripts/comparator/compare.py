#!/usr/bin/env python3
"""Receipt-pinned, isolated typed comparison. Invoke from a trusted installation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from independent.replay import ALLOWED_AXIOMS, checker_config, load_tools, sha
try:
    from .canonical import read_export, compare, digest
    from .sandbox import Sandbox, limited_run
except ImportError:
    from canonical import read_export, compare, digest
    from sandbox import Sandbox, limited_run

# All names used specially by pinned nanoda's mk_name_cache (util.rs), plus
# the three permitted axioms. Extension reductions dispatch by name rather
# than authenticating arithmetic/String bodies; never allow a hole in this
# foundation or any of its transitive dependencies.
FOUNDATION = frozenset(ALLOWED_AXIOMS | {
    'eagerReduce', 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    'String', 'String.ofList', 'Char', 'Char.ofNat', 'List', 'List.nil', 'List.cons',
    'Bool.true', 'Bool.false', 'Nat', 'Nat.zero', 'Nat.succ',
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.mod', 'Nat.div',
    'Nat.beq', 'Nat.ble', 'Nat.gcd', 'Nat.xor', 'Nat.land', 'Nat.lor',
    'Nat.shiftLeft', 'Nat.shiftRight',
})

IDENT = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
EXCLUDED = {'.git', '.lake', 'build', 'work', '__pycache__'}
DEFAULT_LIMITS = {'memory_mb': 6144, 'address_mb': 65536, 'cpu_seconds': 600, 'wall_seconds': 900,
                  'file_mb': 1024, 'temp_mb': 512, 'work_mb': 2048, 'source_mb': 256, 'source_files': 20000}


def relative(path):
    p = Path(path)
    if not isinstance(path, str) or p.is_absolute() or '..' in p.parts or not p.parts or str(p) != path:
        raise ValueError('unsafe relative path')
    return p


def safe_child(folder, path):
    """Never let a candidate-created parent symlink redirect a host-side read."""
    folder = Path(folder).resolve()
    result = folder
    for component in relative(path).parts:
        result = result / component
        if result.is_symlink(): raise ValueError('artifact path contains a symbolic link')
    if not result.resolve(strict=True).is_relative_to(folder) or not result.is_file():
        raise ValueError('artifact is missing or leaves candidate tree')
    return result


def snapshot(folder, filtered=True, limits=None):
    result = {}
    total_bytes = total_directories = 0
    limits = limits or DEFAULT_LIMITS
    folder = Path(folder).resolve()
    for base, dirs, files in os.walk(folder, followlinks=False):
        base = Path(base)
        if any((base / d).is_symlink() for d in dirs):
            raise ValueError('symbolic links are forbidden in a submission/trust tree')
        dirs[:] = sorted(d for d in dirs if not filtered or d not in EXCLUDED)
        total_directories += len(dirs)
        if filtered and total_directories > limits['source_files']:
            raise ValueError('source directory count exceeds approved bounds')
        for name in sorted(files):
            p = base / name
            if p.is_symlink() and not filtered:
                resolved = p.resolve(strict=True)
                if not resolved.is_relative_to(folder) or not resolved.is_file():
                    raise ValueError('toolchain link leaves approved tree')
                result[str(p.relative_to(folder))] = 'link:' + os.readlink(p) + ':' + sha(resolved)
                continue
            if p.is_symlink() or not p.is_file():
                raise ValueError('only ordinary files are permitted')
            if filtered and (name.endswith(('.olean', '.ilean', '.so', '.o', '.a', '.pyc'))):
                raise ValueError('prebuilt artifacts outside ignored build directories are forbidden')
            if filtered:
                total_bytes += p.stat().st_size
                if total_bytes > limits['source_mb'] * 1048576 or len(result) >= limits['source_files']:
                    raise ValueError('source tree exceeds approved bounds')
            result[str(p.relative_to(folder))] = sha(p)
    return result


def copy_sources(source, destination, files, limits):
    if len(files) > limits['source_files'] or sum((source / f).stat().st_size for f in files) > limits['source_mb'] * 1048576:
        raise ValueError('source tree exceeds approved bounds')
    for file in files:
        target = destination / relative(file)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / file, target)
    if snapshot(destination, limits=limits) != files:
        raise ValueError('source changed while copying')


def parse_receipt(path, expected):
    if Path(path).stat().st_size > 1048576: raise ValueError('approval receipt exceeds size bound')
    if not re.fullmatch('[0-9a-f]{64}', expected or '') or sha(path) != expected:
        raise ValueError('approval receipt does not match the externally supplied approval digest')
    receipt = json.loads(Path(path).read_text())
    required = {'schema', 'reference_sha256', 'toolchain_sha256', 'tools_pins', 'modules', 'build_targets',
                'roots', 'protected_declarations', 'implementation_declarations', 'protected_files', 'artifacts', 'limits', 'tool_binaries', 'sandbox_sha256'}
    if set(receipt) != required or receipt['schema'] != 1:
        raise ValueError('unsupported approval receipt schema')
    for field in ['modules', 'build_targets', 'roots', 'protected_declarations']:
        values = receipt[field]
        if not isinstance(values, list) or not values or len(set(values)) != len(values) or not all(IDENT.fullmatch(x) for x in values):
            raise ValueError('invalid approved ' + field)
    holes = receipt['implementation_declarations']
    if not isinstance(holes, list) or len(set(holes)) != len(holes) or not all(IDENT.fullmatch(x) for x in holes) or set(holes) & (set(receipt['protected_declarations']) | FOUNDATION):
        raise ValueError('invalid or conflicting approved implementation declarations')
    if not receipt['protected_files'] or not receipt['artifacts']:
        raise ValueError('approval must bind protected source and at least one emitted artifact')
    for path in receipt['protected_files']: relative(path)
    if set(receipt['limits']) != set(DEFAULT_LIMITS) or not all(type(v) is int and v > 0 for v in receipt['limits'].values()):
        raise ValueError('invalid resource limits')
    if len({a['path'] for a in receipt['artifacts']}) != len(receipt['artifacts']):
        raise ValueError('duplicate approved artifact path')
    for artifact in receipt['artifacts']:
        if set(artifact) != {'path', 'module', 'bytes', 'correctness_root', 'generate'}:
            raise ValueError('invalid approved artifact specification')
        relative(artifact['path'])
        if artifact['correctness_root'] not in receipt['roots'] or not all(IDENT.fullmatch(artifact[k]) for k in ['module','bytes']):
            raise ValueError('artifact is not bound to an approved theorem')
        if not isinstance(artifact['generate'], list) or not artifact['generate'] or not all(isinstance(x,str) and '\0' not in x for x in artifact['generate']):
            raise ValueError('invalid approved artifact generation command')
    return receipt


def lean_literal(data):
    if any(b not in (9,10,13) and not 32 <= b < 127 for b in data):
        raise ValueError('artifact byte binding currently requires printable ASCII and tab/CR/LF')
    return json.dumps(data.decode('ascii'))


def run_comparison(reference, candidate, receipt_path, approval_sha256, toolchain, tools_manifest,
                   output, level='L3', bwrap='bwrap'):
    reference, candidate, output = map(lambda p: Path(p).resolve(), [reference,candidate,output])
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / 'acceptance.json'; report_path.unlink(missing_ok=True)
    if level not in ('L2','L3'): raise ValueError('comparator supports L2 and L3 only')
    receipt = parse_receipt(receipt_path, approval_sha256)
    tools = load_tools(tools_manifest)
    tools_manifest_sha = sha(tools_manifest)
    tool_manifest = json.loads(Path(tools_manifest).read_text())
    bwrap = shutil.which(bwrap) or bwrap
    if sha(bwrap) != receipt['sandbox_sha256']:
        raise ValueError('sandbox executable is not approved')
    if {k: sha(v) for k,v in tools.items()} != receipt['tool_binaries']:
        raise ValueError('checker binaries are not independently approved')
    if tool_manifest['pins'] != receipt['tools_pins']:
        raise ValueError('tools are not covered by approval')
    baseline, submission = snapshot(reference, limits=receipt['limits']), snapshot(candidate, limits=receipt['limits'])
    if digest(baseline) != receipt['reference_sha256']:
        raise ValueError('reference tree differs from independently approved reference')
    # Toolchain paths may contain ordinary version-manager symlinks. Resolve the
    # root, and bind each internal file link and its resolved content to the digest.
    if digest(snapshot(toolchain, filtered=False)) != receipt['toolchain_sha256']:
        raise ValueError('toolchain differs from independently approved toolchain')
    for file, expected in receipt['protected_files'].items():
        if baseline.get(file) != expected or submission.get(file) != expected:
            raise ValueError('protected source differs: ' + file)
    sandbox = Sandbox(bwrap, toolchain, tools['exporter'], tools['checker'], receipt['limits'])
    exports, artifact_hashes, bound_roots = {}, {}, []
    with tempfile.TemporaryDirectory(prefix='hdlean-comparator-') as tmp:
        temp = Path(tmp)
        sandbox.probe(temp, output / 'sandbox.log')
        for tag, source, files in [('reference',reference,baseline), ('candidate',candidate,submission)]:
            stage = temp / tag; stage.mkdir()
            copy_sources(source, stage, files, receipt['limits'])
            protected = [(reference / f, f) for f in receipt['protected_files']]
            sandbox.run(stage, ['/toolchain/bin/lake', 'build', *receipt['build_targets']],
                        output / (tag + '-build.log'), writable=True, protected=protected)
            for k, artifact in enumerate(receipt['artifacts']):
                sandbox.run(stage, artifact['generate'], output / f'{tag}-artifact-{k}.log',
                            writable=True, protected=protected)
            if snapshot(stage, limits=receipt['limits']) != files:
                raise ValueError('build modified source inputs: ' + tag)
            for module in receipt['modules']:
                sandbox.run(stage, ['/toolchain/bin/leanchecker', '--fresh', module],
                            output / f'{tag}-kernel-{module}.log')
            extra_modules, extra_roots, bindings = [], [], {}
            certdir = temp / (tag + '-bindings'); certdir.mkdir()
            if tag == 'candidate':
                src = []
                artifact_total = 0
                for k, artifact in enumerate(receipt['artifacts']):
                    file = safe_child(stage, artifact['path'])
                    if file.is_symlink() or not file.is_file(): raise ValueError('artifact is missing or is a link')
                    if file.stat().st_size > min(receipt['limits']['file_mb'], 64) * 1048576:
                        raise ValueError('artifact exceeds literal-binding size bound')
                    artifact_total += file.stat().st_size
                    if artifact_total > 64 * 1048576:
                        raise ValueError('aggregate artifact bytes exceed literal-binding size bound')
                    artifact_hashes[artifact['path']] = sha(file)
                    src.append('import ' + artifact['module'])
                # A kernel theorem binds the exact literal bytes. Native evaluation
                # of an implementation-overridden String is never used as evidence.
                src += ['set_option maxRecDepth 65536', 'set_option maxHeartbeats 16000000']
                for k, artifact in enumerate(receipt['artifacts']):
                    data = safe_child(stage, artifact['path']).read_bytes()
                    root = f'HDLeanComparatorBindings.artifact_{k}'
                    src += [f'theorem {root} : {artifact["bytes"]} = {lean_literal(data)} := by decide +kernel']
                    extra_roots.append(root)
                    bindings[root] = (artifact["bytes"], data.decode("ascii"))
                (certdir / 'HDLeanComparatorBindings.lean').write_text('\n'.join(src) + '\n')
                sandbox.run(stage, ['/toolchain/bin/lean', '-j2', '-R', '/out', '-o', '/out/HDLeanComparatorBindings.olean',
                                    '/out/HDLeanComparatorBindings.lean'], output / 'byte-binding-kernel.log', output=certdir, output_writable=True)
                extra_modules.append('HDLeanComparatorBindings')
                bound_roots = extra_roots
            export = output / (tag + '.ndjson')
            roots = list(dict.fromkeys(receipt['roots'] + receipt['protected_declarations'] + receipt['implementation_declarations'] + sorted(FOUNDATION) + extra_roots))
            sandbox.run(stage, ['/tools/exporter', *dict.fromkeys(['Init'] + receipt['modules'] + extra_modules), '--', *roots], export, output=certdir)
            # Both levels require independent authentication: native initializers
            # in an adversarial import must not be able to forge exporter output.
            shutil.copyfile(export, certdir / 'proofs.ndjson')
            cfg = checker_config('/out/proofs.ndjson'); cfg['export_file_path'] = '/out/proofs.ndjson'
            (certdir / 'nanoda.json').write_text(json.dumps(cfg))
            sandbox.run(stage, ['/tools/checker', '/out/nanoda.json'], output / (tag + '-nanoda.log'), output=certdir)
            if (output / (tag + '-nanoda.log')).stat().st_size > 1024:
                raise ValueError('independent checker success output exceeds bound')
            if not re.fullmatch(r'Checked ([1-9][0-9]*) declarations with no errors\n?', (output / (tag + '-nanoda.log')).read_text()):
                raise ValueError('independent checker did not report success')
            parse_config = {'audit_roots':receipt['roots'] + extra_roots, 'max_bytes': receipt['limits']['file_mb'] * 1048576,
                            'type_roots':[a['correctness_root'] for a in receipt['artifacts']],
                            'bindings':bindings, 'protect_types':receipt['roots'] if tag == 'reference' else [],
                            'protect_declarations':(receipt['protected_declarations'] + receipt['implementation_declarations'] + sorted(FOUNDATION)) if tag == 'reference' else [],
                            'implementation_declarations':receipt['implementation_declarations'],
                            'foundation_declarations':sorted(FOUNDATION) if tag == 'reference' else []}
            config_path = output / (tag + '-parse.json')
            config_path.write_text(json.dumps(parse_config))
            parsed_path = output / (tag + '-declarations.json')
            limited_run([sys.executable, str(HERE / 'canonical.py'), str(export), str(config_path)],
                        parsed_path, receipt['limits'])
            if parsed_path.stat().st_size > 64 * 1048576:
                raise ValueError('canonical declaration summary exceeds size bound')
            exports[tag] = json.loads(parsed_path.read_text())
            for artifact in receipt['artifacts']:
                if artifact['bytes'] not in exports[tag][artifact['correctness_root']]['type_constants']:
                    raise ValueError('approved artifact theorem does not mention its byte definition')
        protected_closure = sorted(n for n,d in exports['reference'].items() if d['protected'])
        checked = compare(exports['reference'], exports['candidate'], receipt['roots'], protected_closure, receipt['implementation_declarations'])
    if snapshot(reference, limits=receipt['limits']) != baseline or snapshot(candidate, limits=receipt['limits']) != submission or sha(receipt_path) != approval_sha256:
        raise ValueError('inputs changed during comparison')
    if sha(tools_manifest) != tools_manifest_sha or {k: sha(v) for k,v in tools.items()} != receipt['tool_binaries']:
        raise ValueError('independent checker tools changed during comparison')
    if digest(snapshot(toolchain, filtered=False)) != receipt['toolchain_sha256'] or sha(bwrap) != receipt['sandbox_sha256']:
        raise ValueError('trusted tools changed during comparison')
    result = {'schema':1, 'passed':True, 'level':level, 'approval_sha256':approval_sha256,
              'reference_sha256':digest(baseline), 'candidate_sha256':digest(submission),
              'typed_statements':checked, 'protected_declarations':[n for n in protected_closure if n not in receipt['implementation_declarations']],
              'implementation_declarations':receipt['implementation_declarations'],
              'artifact_sha256':artifact_hashes, 'byte_binding_roots':bound_roots,
              'foundation_declarations':sorted(n for n,d in exports['reference'].items() if d['foundation']),
              'sandbox':'bubblewrap --unshare-all; read-only checking; no network',
              'fresh_kernel':True, 'nanoda':True, 'native_axioms':[],
              'limits':receipt['limits']}
    report_path.write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ['reference','candidate','receipt','approval-sha256','toolchain','tools','output']:
        p.add_argument('--' + arg, required=True)
    p.add_argument('--level', choices=['L2','L3'], default='L3')
    p.add_argument('--bwrap', default='bwrap')
    a = p.parse_args()
    run_comparison(a.reference,a.candidate,a.receipt,a.approval_sha256,a.toolchain,a.tools,a.output,a.level,a.bwrap)
    print('Accepted independently approved block at ' + a.level)

if __name__ == '__main__': main()
