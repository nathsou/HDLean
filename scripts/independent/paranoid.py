#!/usr/bin/env python3
"""Run all bundled kernels through Lake with a hash-checked nanoda resource adapter.

Lean 4.35's Lake hardcodes four nanoda workers, whose fixed stacks overflow on
large closures. A separate toolchain view retains the release files and runs the
unchanged bundled nanoda serially, on the OS stack. The installed toolchain is
never rewritten. The normal namespace sandbox remains mandatory by default.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys

from replay import load_tools, sha

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def prepare(tools_manifest, prefix):
    tools = load_tools(tools_manifest)
    source = tools['checker'].parent.parent.resolve()
    if any(binary.parent != source / 'bin' for binary in tools.values()):
        raise ValueError('bundled tools must share one release toolchain')
    prefix = Path(prefix).resolve()
    if prefix == source or prefix in source.parents or source in prefix.parents:
        raise ValueError('toolchain view must be separate from the installed toolchain')
    prefix.mkdir(parents=True, exist_ok=True)
    # Hard links keep this view self-contained inside Lake's read-only toolchain
    # mount. A copied file is used when the cache is on a different filesystem.
    for directory, dirs, files in os.walk(source):
        relative = Path(directory).relative_to(source)
        target = prefix / relative
        target.mkdir(parents=True, exist_ok=True)
        for name in dirs[:]:
            original = Path(directory) / name
            if original.is_symlink():
                destination = target / name
                if not destination.is_symlink():
                    destination.symlink_to(os.readlink(original))
                dirs.remove(name)
        for name in files:
            if relative == Path('bin') and name == tools['checker'].name:
                continue
            original, destination = Path(directory) / name, target / name
            if destination.exists() or destination.is_symlink():
                if original.is_symlink():
                    if not destination.is_symlink() or os.readlink(destination) != os.readlink(original):
                        raise ValueError('modified toolchain-view symlink')
                elif not os.path.samestat(original.stat(), destination.stat()) and sha(original) != sha(destination):
                    raise ValueError('modified toolchain-view file')
                continue
            if original.is_symlink():
                destination.symlink_to(os.readlink(original))
            else:
                try:
                    os.link(original, destination)
                except OSError:
                    shutil.copy2(original, destination)
    native = prefix / 'bin/nanoda-native'
    if native.exists():
        if sha(native) != sha(tools['checker']):
            raise ValueError('modified native checker in toolchain view')
    else:
        shutil.copy2(tools['checker'], native)
    adapter = prefix / 'bin' / tools['checker'].name
    source_adapter = HERE / 'nanoda_serial.py'
    body = source_adapter.read_text().replace('@HDLEAN_CHECKER@', str(native)).replace(
        '@HDLEAN_CHECKER_SHA256@', sha(native)).replace(
        'REJECT_UNUSED_AXIOMS = True', 'REJECT_UNUSED_AXIOMS = False')
    if adapter.exists() or adapter.is_symlink():
        if adapter.is_symlink() or adapter.read_text() != body:
            raise ValueError('modified checker adapter in toolchain view')
    else:
        adapter.write_text(body)
        adapter.chmod(0o755)
    # Lake exports unused built-in axiom declarations such as sorryAx. Its
    # whole-project policy omits unpermitted declarations and rejects every use;
    # nanoda then reports an unknown constant if any proof refers to one. Lake's
    # checkUsedAxioms additionally audits the complete export after replay.
    # Root-only exports and comparator adapters retain their stricter default.
    # The other four kernels are byte-for-byte the bundled release executables.
    names = ['leanchecker-paranoid','lean4lean','con-leche','con-ron']
    digests = {name: sha(source / 'bin' / name) for name in names}
    for name, digest in digests.items():
        if sha(prefix / 'bin' / name) != digest:
            raise ValueError('bundled checker digest mismatch: ' + name)
    return {'source': str(source), 'prefix': str(prefix), 'bundled': digests,
            'nanoda_native_sha256': sha(native), 'nanoda_adapter_sha256': sha(adapter),
            'adapter_source_sha256': sha(source_adapter)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tools', type=Path, default=ROOT / 'work/independent-tools/tools.json')
    parser.add_argument('--prefix', type=Path, help='separate cached release toolchain view')
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--report', type=Path, default=ROOT / 'build/paranoid-kernels.json')
    parser.add_argument('--inadvisably-no-sandbox', action='store_true',
                        help='local diagnostic only; never records isolated acceptance')
    args = parser.parse_args()
    args.report.unlink(missing_ok=True)
    args.prefix = args.prefix or ROOT / 'work/paranoid-toolchains' / sha(HERE / 'nanoda_serial.py')[:16]
    before = prepare(args.tools, args.prefix)
    env = dict(os.environ, LEAN_SYSROOT=str(args.prefix.resolve()))
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    command = [str(args.prefix.resolve() / 'bin/lake'), 'check', '--paranoid']
    if args.inadvisably_no_sandbox:
        command.append('--inadvisably-no-sandbox')
    # Stream progress so a resource-limited run retains the engines that finished.
    process = subprocess.Popen(command,cwd=args.project,env=env,text=True,
                               stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    lines = []
    for line in process.stdout:
        sys.stdout.write(line)
        sys.stdout.flush()
        lines.append(line)
    if process.wait():
        raise SystemExit(process.returncode)
    output = ''.join(lines)
    for name in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:
        if name + ' kernel accepts the solution' not in output:
            raise ValueError('missing unconditional kernel acceptance: ' + name)
    axiom_lines = [line for line in output.splitlines() if line.startswith('Uses axioms: ')]
    if len(axiom_lines) != 1 or set(axiom_lines[0].removeprefix('Uses axioms: ').split(', ')) - {'propext','Classical.choice','Quot.sound'}:
        raise ValueError('missing or nonstandard whole-project axiom audit')
    after = prepare(args.tools, args.prefix)
    if before != after:
        raise ValueError('checker identity changed during replay')
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps({'schema': 1, 'passed': True,
        'isolated': not args.inadvisably_no_sandbox, 'command': command, **after}, indent=2)+'\n')
    print('All bundled kernels accepted; report: ' + str(args.report))


if __name__ == '__main__':
    main()
