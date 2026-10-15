#!/usr/bin/env python3
"""Measure FPGA mapped utilization and routed timing on iCE40HX8K or ECP5-25K."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def command(args, cwd, log, env=None):
    result = subprocess.run([str(a) for a in args], cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, timeout=1800)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'command failed ({result.returncode}); see {log}')
    return result.stdout.strip()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('design', choices=['counter', 'fifo', 'pipeline', 'ram', 'toy16'])
    p.add_argument('--device', choices=['ice40-hx8k','ecp5-25k'], default='ice40-hx8k')
    p.add_argument('--width', type=int, default=8)
    p.add_argument('--frequency-mhz', type=float, default=12)
    p.add_argument('--seed', type=int, default=1)
    p.add_argument('--yosys', default=os.environ.get('YOSYS', 'yosys'))
    p.add_argument('--abc', default=os.environ.get('ABC', 'yosys-abc'))
    p.add_argument('--nextpnr', default=os.environ.get('NEXTPNR'))
    p.add_argument('--chipdb-model', type=Path, help='chipdb-8k.bin used by nextpnr; defaults to installed shared model')
    p.add_argument('--output', type=Path, default=ROOT / 'build/physical')
    a = p.parse_args()
    if not 0 <= a.width <= 64 or not 0 < a.frequency_mhz <= 1000 or not 0 <= a.seed < 2**32:
        p.error('invalid width, frequency, or seed')
    a.nextpnr = a.nextpnr or ('nextpnr-ecp5' if a.device == 'ecp5-25k' else 'nextpnr-ice40')
    tools = {}
    for name in ['yosys', 'abc', 'nextpnr']:
        binary = shutil.which(getattr(a, name))
        if not binary:
            p.error(f'missing {name}: {getattr(a,name)}')
        tools[name] = Path(binary).resolve()
    embedded = tools['nextpnr'].parent.parent / 'libexec' / tools['nextpnr'].name
    model = a.chipdb_model or ((embedded if embedded.is_file() else tools['nextpnr']) if a.device == 'ecp5-25k' else
                              tools['nextpnr'].parent.parent / 'share/nextpnr/ice40/chipdb-8k.bin')
    if not model.is_file():
        p.error('missing device model; pass --chipdb-model with the model used by nextpnr')
    work = a.output.resolve() / f'{a.design}-{a.width}-{a.device}'
    work.mkdir(parents=True, exist_ok=True)
    report_path = work / 'report.json'
    report_path.unlink(missing_ok=True)
    env = dict(os.environ, PATH=str(tools['abc'].parent) + os.pathsep + os.environ.get('PATH', ''))
    command([ROOT / '.lake/build/bin/hdlean', 'emit', a.design, 'sv', 'input.sv', a.width],
            work, work / 'emit.log', env)
    module = {'counter':'hd_decade', 'fifo':f'hd_fifo2_w{a.width}',
              'pipeline':f'hd_pipeline3_w{a.width}', 'ram':f'hd_ram_16x{a.width}', 'toy16':'hd_toy16'}[a.design]
    # Filenames/module identifiers are controlled; no user path enters Yosys source.
    flow = 'synth_ecp5' if a.device == 'ecp5-25k' else 'synth_ice40'
    command([tools['yosys'], '-Q', '-T', '-p',
             f'read_verilog -sv input.sv; {flow} -top {module} -json mapped.json'],
            work, work / 'synthesis.log', env)
    if a.device == 'ecp5-25k':
        physical_args = ['--25k','--package','CABGA381','--speed','6','--textcfg','routed.config','--lpf-allow-unconstrained']
        configured = 'routed.config'
    else:
        physical_args = ['--hx8k','--package','ct256','--asc','routed.asc','--pcf-allow-unconstrained']
        configured = 'routed.asc'
    command([tools['nextpnr'], *physical_args, '--json', 'mapped.json',
             '--freq', a.frequency_mhz, '--seed', a.seed,
             '--report', 'routed.json', '--detailed-timing-report'],
            work, work / 'routing.log', env)
    measured = json.loads((work / 'routed.json').read_text())
    if not measured.get('fmax') or not measured.get('utilization'):
        raise ValueError('missing measured timing or utilization')
    if any(v['achieved'] < a.frequency_mhz or v['constraint'] != a.frequency_mhz
           for v in measured['fmax'].values()):
        raise ValueError('routed timing did not meet the requested clock constraint')
    if any(v['used'] > v['available'] for v in measured['utilization'].values()):
        raise ValueError('device resource budget exceeded')
    versions = {name: command([binary, '-V' if name == 'yosys' else '--version'], work,
                              work / f'{name}-version.log', env)
                for name,binary in tools.items() if name != 'abc'}
    report = {'schema':1, 'passed':True, 'kind':'measured-after-placement-and-routing',
              'design':a.design, 'width':a.width, 'device':a.device, 'package':'CABGA381' if a.device == 'ecp5-25k' else 'CT256',
              'seed':a.seed, 'target_frequency_mhz':a.frequency_mhz,
              'chipdb_model':{'path':str(model.resolve()),'sha256':digest(model)},
              'tools':{k:{'path':str(v),'sha256':digest(v),'version':versions.get(k),
                         'implementation_sha256':digest(v.parent.parent/'libexec'/v.name)
                         if (v.parent.parent/'libexec'/v.name).is_file() else digest(v)} for k,v in tools.items()},
              'artifacts':{name:digest(work/name) for name in ['input.sv','mapped.json','routed.json',configured]},
              'fmax_mhz':measured['fmax'], 'utilization':measured['utilization'],
              'power':None, 'io_constraints':'Automatic package pin placement; no external input/output delay assumptions.',
              'limitations':'Device-model register timing; no board measurement, ASIC area, external interface timing, or power claim.'}
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(report_path)


if __name__ == '__main__':
    main()
