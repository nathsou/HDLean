#!/usr/bin/env python3
"""Check literal headline types and the meaning of their transitive dependencies.

Recording a candidate writes review material only. The approved manifest digest
must come from outside the submission; it pins this file and declarations.json.
"""
import argparse
import json
from pathlib import Path
import subprocess

from comparator.canonical import read_export, compare
from comparator.compare import FOUNDATION

ROOT = Path(__file__).resolve().parents[1]


def audit(lake, output, record=False):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    claims = json.loads((ROOT / 'verification/claims.json').read_text())
    roots = sorted(claims.values())
    configs = list(ROOT.glob('Designs/*/comparator.json')) + [ROOT / 'verification/comparator.json']
    holes = sorted({n for p in configs for n in json.loads(p.read_text())['definition_names']})
    path = output / 'statements.ndjson'
    with path.open('w') as stream, (output / 'export.log').open('w') as errors:
        p = subprocess.run([str(lake), 'env', 'leanexport', 'Verification.Solution', '--',
                            *roots, *holes, *sorted(FOUNDATION)], cwd=ROOT,
                           stdout=stream, stderr=errors, timeout=600)
    if p.returncode:
        raise RuntimeError('statement export failed; see ' + str(output / 'export.log'))
    actual = read_export(path, protect_types=roots, implementation_declarations=holes,
                         foundation_declarations=FOUNDATION)
    protected = sorted(n for n, d in actual.items() if d['protected'])
    retained = sorted(set(protected) | set(roots) | set(holes))
    current = {n: actual[n] for n in retained}
    reference = ROOT / 'verification/declarations.json'
    if record:
        reference.write_text(json.dumps({'schema': 1, 'approval': 'review-required',
            'claims': claims, 'roots': roots, 'implementation': holes, 'protected': protected,
            'declarations': current}, indent=2, sort_keys=True) + '\n')
        return {'approval': 'review-required', 'recorded_declarations': len(current)}
    approved = json.loads(reference.read_text())
    if (approved.get('schema') != 1 or approved['claims'] != claims or
            approved['roots'] != roots or approved['implementation'] != holes or
            approved['protected'] != protected):
        raise ValueError('frozen statement coverage or dependency closure changed')
    compare(approved['declarations'], actual, roots, protected, holes)
    return {'checked_statements': len(roots), 'protected_declarations': len(protected),
            'implementation_holes': holes}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/statement-audit')
    parser.add_argument('--record-candidate', action='store_true')
    args = parser.parse_args()
    print(json.dumps(audit(args.lake, args.output, args.record_candidate)))
