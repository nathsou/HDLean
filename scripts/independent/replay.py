#!/usr/bin/env python3
"""Export explicit theorem roots and independently replay their entire dependency closure."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = json.loads((HERE / 'pins.json').read_text())
ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def load_tools(path):
    manifest = json.loads(Path(path).read_text())
    if manifest.get('schema') != 1 or manifest.get('pins') != PINS:
        raise ValueError('independent tool manifest does not match the pinned tools')
    result = {}
    for key in ('exporter', 'checker'):
        info = manifest['binaries'][key]
        executable = Path(info['path']).resolve(strict=True)
        if sha(executable) != info['sha256']:
            raise ValueError(f'independent {key} binary digest mismatch')
        result[key] = executable
    return result


def audit_export(path, roots):
    """Reject empty/missing roots, wrong versions, unsafe code, and every foreign axiom.

    This checks coverage/policy, not proof correctness. Nanoda separately parses and
    typechecks the original, unmodified export; no declarations are filtered out.
    """
    if not roots or len(roots) != len(set(roots)):
        raise ValueError('theorem roots must be nonempty and unique')
    names = {0: ''}
    theorems, axioms = set(), set()
    with Path(path).open() as stream:
        metadata = json.loads(next(stream))
        if metadata.get('meta', {}).get('lean', {}).get('version') != PINS['lean']:
            raise ValueError('export Lean version differs from pinned toolchain')
        if metadata['meta'].get('format', {}).get('version') != PINS['export_format']:
            raise ValueError('unsupported export format')
        for line in stream:
            item = json.loads(line)
            if 'in' in item:
                idx = item['in']
                if type(idx) is not int or idx != len(names):
                    raise ValueError('duplicate or out-of-order name index')
                component = item.get('str', item.get('num'))
                prefix = names[component['pre']]
                suffix = component.get('str', str(component.get('i')))
                names[idx] = prefix + ('.' if prefix else '') + suffix
            for kind in ('axiom', 'def', 'opaque', 'thm'):
                if kind not in item:
                    continue
                declaration = item[kind]
                name = names[declaration['name']]
                if declaration.get('isUnsafe', False) or declaration.get('safety', 'safe') != 'safe':
                    raise ValueError(f'unsafe/partial declaration in export: {name}')
                if kind == 'axiom':
                    if name not in ALLOWED_AXIOMS:
                        raise ValueError(f'forbidden axiom: {name}')
                    axioms.add(name)
                elif kind == 'thm':
                    if name in theorems:
                        raise ValueError(f'duplicate theorem in export: {name}')
                    theorems.add(name)
    missing = set(roots) - theorems
    if missing:
        raise ValueError(f'required theorem roots missing from export: {sorted(missing)}')
    return {'roots': sorted(roots), 'axioms': sorted(axioms),
            'theorems_in_closure': len(theorems)}


def checker_config(export_path):
    return {'export_file_path': str(Path(export_path).resolve()), 'use_stdin': False,
            'permitted_axioms': sorted(ALLOWED_AXIOMS),
            'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
            'nat_extension': True, 'string_extension': True,
            'pp_declars': [], 'print_axioms': False, 'print_success_message': True}


def checked_run(command, cwd, log, timeout):
    result = subprocess.run(list(map(str, command)), cwd=cwd, text=True,
                            capture_output=True, timeout=timeout)
    Path(log).write_text(result.stdout + result.stderr)
    if result.returncode or 'uncaught exception:' in result.stdout + result.stderr:
        raise RuntimeError(f'proof check failed; see {log}')
    return result.stdout


def replay(project, lake, tools_manifest, output, roots, modules, timeout=600):
    """Callable by the comparator after its fresh build and trust-boundary checks."""
    project, output = Path(project).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / 'replay.json'
    result_path.unlink(missing_ok=True)
    if not roots or len(roots) != len(set(roots)) or not modules:
        raise ValueError('provide explicit unique theorem roots and modules')
    if not all(IDENTIFIER.fullmatch(x) for x in [*roots, *modules]):
        raise ValueError('invalid theorem/module identifier')
    manifest_digest = sha(tools_manifest)
    tools = load_tools(tools_manifest)
    export_path = output / 'proofs.ndjson'
    export_log = output / 'export.log'
    command = [str(lake), 'env', str(tools['exporter']), *modules, '--', *roots]
    # Export is a stream so larger proof closures do not accumulate in Python memory.
    with export_path.open('w') as stream, export_log.open('w') as errors:
        result = subprocess.run(command, cwd=project, stdout=stream, stderr=errors, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'proof export failed; see {export_log}')
    audit = audit_export(export_path, roots)
    export_digest = sha(export_path)
    config_path = output / 'nanoda.json'
    config_path.write_text(json.dumps(checker_config(export_path), indent=2) + '\n')
    stdout = checked_run([tools['checker'], config_path], project, output / 'nanoda.log', timeout)
    success = re.fullmatch(r'Checked ([1-9][0-9]*) declarations with no errors\n?', stdout)
    if not success:
        raise RuntimeError('nanoda did not report an unqualified successful replay')
    # Check binaries again: do not issue a success report if tools changed during replay.
    load_tools(tools_manifest)
    if sha(tools_manifest) != manifest_digest or sha(export_path) != export_digest:
        raise RuntimeError('tool manifest or proof export changed during replay')
    report = {'schema': 1, 'passed': True, 'checker': 'nanoda', 'pins': PINS,
              'checked_declarations': int(success.group(1)), **audit,
              'modules': list(modules), 'export_sha256': export_digest,
              'tools_manifest_sha256': manifest_digest,
              'checker_sha256': sha(tools['checker']), 'exporter_sha256': sha(tools['exporter']),
              'checked_at': datetime.now(timezone.utc).isoformat()}
    result_path.write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--tools', type=Path, default=ROOT / 'work/independent-tools/tools.json')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/independent')
    parser.add_argument('--module', action='append', required=True)
    parser.add_argument('--theorem', action='append', required=True)
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    report = replay(args.project, args.lake, args.tools, args.output,
                    args.theorem, args.module, args.timeout)
    print(f'Independently replayed {len(report["roots"])} roots / '
          f'{report["checked_declarations"]} declarations; {args.output / "replay.json"}')


if __name__ == '__main__':
    main()
