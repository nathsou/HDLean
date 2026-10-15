#!/usr/bin/env python3
"""Bind an exact backend file to a kernel and independently replayed circuit proof."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

if __package__:
    from .byte_certificate import generate, sha
    from .replay import replay
else:
    from byte_certificate import generate, sha
    from replay import replay


def certify(project, lake, tools, output, artifact, graph_aiger, design, width, format,
            memory_mb=6144, timeout=600):
    project, output = Path(project).resolve(), Path(output).resolve()
    artifact, graph_aiger = Path(artifact).resolve(), Path(graph_aiger).resolve()
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / 'certificate.json'
    report_path.unlink(missing_ok=True)
    artifact_data, graph_data = artifact.read_bytes(), graph_aiger.read_bytes()
    identity = sha(artifact_data + b'\0' + graph_data + f'{design}:{width}:{format}'.encode())
    module = 'HDLeanArtifact_' + identity[:32]
    source, manifest = generate(artifact_data, graph_data, design, width, format, module)
    source_path = output / (module + '.lean')
    source_path.write_bytes(source)
    # An isolated content-addressed module avoids replacing any ordinary project module.
    olean = project / '.lake/build/lib/lean' / (module + '.olean')
    olean.parent.mkdir(parents=True, exist_ok=True)
    olean.unlink(missing_ok=True)
    start = time.monotonic()
    with (output / 'kernel.log').open('wb') as log:
        result = subprocess.run([str(lake), 'env', 'lean', '-M', str(memory_mb),
                                 '-R', str(output), '-o', str(olean), str(source_path)],
                                cwd=project, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'kernel byte certificate failed; see {output / "kernel.log"}')
    kernel_seconds = time.monotonic() - start
    # Execute only the already compiled byte definition, then compare every byte.
    # The executable comparison is a binding check, never a substitute for proof replay.
    runner = output / 'ReadCertificateBytes.lean'
    runner.write_text('import ' + module + '\n')
    result = subprocess.run([str(lake), 'env', 'lean', '--run', str(runner)], cwd=project,
                            capture_output=True, timeout=timeout)
    (output / 'byte-binding.log').write_bytes(result.stderr)
    if result.returncode or result.stdout != artifact_data:
        raise RuntimeError('compiled certificate does not encode the exact artifact bytes')
    independent = replay(project, lake, tools, output / 'independent',
                         manifest['roots'], [module], timeout)
    if artifact.read_bytes() != artifact_data or graph_aiger.read_bytes() != graph_data:
        raise RuntimeError('artifact or graph candidate changed during certification')
    if source_path.read_bytes() != source:
        raise RuntimeError('certificate source changed during certification')
    report = {**manifest, 'passed': True, 'module': module,
              'kernel_seconds': round(kernel_seconds, 3), 'kernel_memory_limit_mb': memory_mb,
              'exact_byte_binding': True, 'independent': independent}
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[2])
    p.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    p.add_argument('--tools', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--artifact', type=Path, required=True)
    p.add_argument('--graph-aiger', type=Path, required=True)
    p.add_argument('--design', choices=['counter', 'fifo', 'pipeline', 'ram', 'toy16', 'circular', 'ring'], required=True)
    p.add_argument('--width', type=int, default=8)
    p.add_argument('--format', choices=['aiger', 'sv', 'rtlil'], required=True)
    p.add_argument('--memory-mb', type=int, default=6144)
    p.add_argument('--timeout', type=int, default=600)
    args = p.parse_args()
    tools = args.tools or args.project / 'work/independent-tools/tools.json'
    report = certify(args.project, args.lake, tools, args.output, args.artifact,
                     args.graph_aiger, args.design, args.width, args.format,
                     args.memory_mb, args.timeout)
    print(json.dumps({'passed': report['passed'], 'artifact_sha256': report['artifact_sha256'],
                      'module': report['module'], 'kernel_seconds': report['kernel_seconds']}))


if __name__ == '__main__':
    main()
