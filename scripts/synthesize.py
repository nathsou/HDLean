#!/usr/bin/env python3
"""Run a real Liberty-mapped synthesis flow. Never estimate physical area from gate count."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('design', choices=['counter', 'fifo', 'pipeline', 'ring', 'ram', 'toy16'])
    p.add_argument('--width', type=int, default=8)
    p.add_argument('--liberty', required=True, type=Path)
    p.add_argument('--yosys', default='yosys')
    p.add_argument('--abc', default='yosys-abc')
    p.add_argument('--output', type=Path, default=ROOT / 'build/physical')
    a = p.parse_args()
    if not a.liberty.is_file():
        p.error('Liberty library does not exist')
    if not shutil.which(a.yosys) or not shutil.which(a.abc):
        p.error('Yosys and ABC are required for physical synthesis')
    a.output.mkdir(parents=True, exist_ok=True)
    # Controlled filenames prevent Yosys command-language injection through user paths.
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        shutil.copyfile(a.liberty, work / 'cells.lib')
        subprocess.run([ROOT / '.lake/build/bin/hdlean', 'emit', a.design, 'sv', work / 'input.sv', str(a.width)], check=True)
        module = 'hd_top'  # the proved bit-level emitter writes one module
        abc = Path(shutil.which(a.abc)).resolve()
        if any(c in str(abc) for c in ' ;"\n'):
            p.error('ABC executable path must not contain whitespace or command delimiters')
        script = (f'read_verilog -sv input.sv; synth -top {module}; dfflibmap -liberty cells.lib; '
                  f'abc -exe {abc} -liberty cells.lib; clean; '
                  'tee -o statistics.json stat -json -liberty cells.lib; write_verilog mapped.v')
        result = subprocess.run([a.yosys, '-p', script], cwd=work, text=True, capture_output=True, check=True)
        statistics = json.loads((work / 'statistics.json').read_text())
        report = {'design': a.design, 'width': a.width, 'kind': 'measured-by-synthesis',
                  'liberty_sha256': hashlib.sha256(a.liberty.read_bytes()).hexdigest(),
                  'yosys': subprocess.check_output([a.yosys, '-V'], text=True).strip(),
                  'statistics': statistics, 'timing': None, 'power': None,
                  'limitations': 'No placement, routing, parasitics, clock-frequency or power claim.'}
        (a.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        (a.output / 'yosys.log').write_text(result.stdout + result.stderr)
        shutil.copyfile(work / 'mapped.v', a.output / 'mapped.v')
    print(a.output / 'report.json')


if __name__ == '__main__':
    main()
