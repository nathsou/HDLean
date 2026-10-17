#!/usr/bin/env python3
"""Build, check and measure the Project Euler solvers on the Alchitry Cu (iCE40-HX8K).

For each problem:

1. `hdlean euler-sim` runs the solver in Lean from reset to `done` and compares
   the answer with the plain-Lean reference (skipped with --no-lean-sim for the
   long runs, where Verilator does the same check);
2. `hdlean euler-emit` writes the solver and the UART reporter as word-level
   SystemVerilog (read back by the proved parser);
3. Verilator runs the emitted solver to `done`: cycle count and answer, which
   must match the reference;
4. Yosys (`synth_ice40`) and nextpnr place and route the board shell, solver and
   reporter: first at an unreachable target to find the achievable Fmax, then at
   the fastest PLL frequency below it (icepll), which must meet timing;
5. icepack writes the bitstream.

The report gives cycles, the PLL clock, compute time (cycles / clock),
utilisation and Fmax, in build/euler/report.json.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / '.lake/build/bin/hdlean'
BOARD = ROOT / 'boards/alchitry-cu'


def tool(name, args):
    path = shutil.which(name, path=args.eda + os.pathsep + os.environ.get('PATH', '')) if args.eda else shutil.which(name)
    if not path:
        raise SystemExit(f'missing tool: {name} (pass --eda with the OSS CAD Suite bin directory)')
    return path


def run(cmd, cwd=None, timeout=7200):
    r = subprocess.run([str(c) for c in cmd], cwd=cwd, text=True, capture_output=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(f'command failed: {" ".join(map(str, cmd))}\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}')
    return r.stdout + r.stderr


HARNESS = r'''
#include "Vsolver.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Vsolver* t = new Vsolver;
  unsigned long long limit = strtoull(argv[1], 0, 10);
  t->i_0_start = 1; t->rst = 1; t->clk = 0; t->eval(); t->clk = 1; t->eval(); t->clk = 0; t->rst = 0; t->eval();
  for (unsigned long long c = 0; c < limit; c++) {
    if (t->o_0_done) { printf("%llu %llu\n", c, (unsigned long long)t->o_1_answer); return 0; }
    t->clk = 1; t->eval(); t->clk = 0; t->eval();
  }
  printf("timeout\n");
  return 1;
}
'''


def verilate(work, module, max_cycles, args):
    vdir = work / 'verilator'
    vdir.mkdir(exist_ok=True)
    (vdir / 'main.cpp').write_text(HARNESS)
    run([tool('verilator', args), '--cc', '--exe', '--build', '-O3', '-Wno-fatal', '--top-module', module,
         '--prefix', 'Vsolver', '-Mdir', vdir / 'obj', work / 'solver.sv', vdir / 'main.cpp'], cwd=vdir)
    out = run([vdir / 'obj/Vsolver', max_cycles]).split()
    return int(out[0]), int(out[1])


def pll(mhz, work, args):
    out = run([tool('icepll', args), '-i', '100', '-o', f'{mhz:.3f}', '-m', '-n', 'pll', '-f', work / 'pll.v'])
    achieved = float(re.search(r'F_PLLOUT:\s*([\d.]+) MHz \(achieved\)', out).group(1))
    return achieved


REPORT_HZ = 50_000_000


def synthesize(work, module, width, args):
    defines = f'verilog_defines -DSOLVER={module} -DANSWER_WIDTH={width}; '
    sources = ' '.join(str(work / f) for f in ('solver.sv', 'report.sv', 'count.sv', 'pll.v'))
    log = run([tool('yosys', args), '-q', '-p',
               defines + f'read_verilog -sv {sources} {BOARD / "euler_top.v"}; '
               f'synth_ice40 -top euler_top -json {work / "top.json"}'], cwd=work)
    (work / 'yosys.log').write_text(log)


def place_route(work, mhz, seed, args):
    (work / 'clocks.py').write_text(f'ctx.addClock("fclk", {mhz:.3f})\nctx.addClock("slow", {REPORT_HZ / 1e6})\nctx.addClock("clk", 100)\n')
    cmd = [tool('nextpnr-ice40', args), '--hx8k', '--package', 'cb132', '--pcf', BOARD / 'cu.pcf',
           '--json', work / 'top.json', '--asc', work / 'top.asc', '--pre-pack', work / 'clocks.py',
           '--seed', seed, '--timing-allow-fail']
    t0 = time.time()
    log = run(cmd, cwd=work)
    (work / f'nextpnr-{seed}.log').write_text(log)
    fmax = [float(m) for m in re.findall(r"Max frequency for clock\s+'fclk[^']*': ([\d.]+) MHz", log)]
    slow = [float(m) for m in re.findall(r"Max frequency for clock\s+'slow[^']*': ([\d.]+) MHz", log)]
    lcs = re.search(r'ICESTORM_LC:\s*(\d+)/\s*(\d+)', log)
    ram = re.search(r'ICESTORM_RAM:\s*(\d+)/\s*(\d+)', log)
    ok_slow = bool(slow) and slow[-1] >= REPORT_HZ / 1e6
    return {'fmax_mhz': (fmax[-1] if fmax and ok_slow else None), 'report_fmax_mhz': slow[-1] if slow else None,
            'lcs': int(lcs.group(1)), 'brams': int(ram.group(1)), 'seconds': round(time.time() - t0, 1)}


def measure(n, args):
    work = ROOT / 'build/euler' / f'p{n:03d}'
    work.mkdir(parents=True, exist_ok=True)
    info = {p['number']: p for p in json.loads(run([CLI, 'euler-list']))}[n]
    result = {'number': n, 'title': info['title'], 'idea': info['idea']}
    if not args.no_lean_sim:
        sim = json.loads(run([CLI, 'euler-sim', n]))
        result['lean_cycles'] = sim['cycles']
        result['reference'] = sim['reference']
    else:
        result['reference'] = json.loads(run([CLI, 'euler-ref', n]))['reference']
    emitted = json.loads(run([CLI, 'euler-emit', n, work, REPORT_HZ]))
    module, width = emitted['module'], emitted['answer_width']
    if module.endswith('_') or not emitted['cells']:
        raise SystemExit(f'p{n}: the solver failed the builder checks (empty module)')
    cycles, answer = verilate(work, module, info['max_cycles'], args)
    result.update(cycles=cycles, answer=answer, cells=emitted['cells'])
    if 'lean_cycles' in result:
        assert result['lean_cycles'] == cycles, f'Lean and Verilator cycle counts differ: {result}'
    assert result['reference'] == answer, f'wrong answer: {result}'
    print(f'p{n}: answer {answer} in {cycles} cycles', flush=True)
    if args.no_pnr:
        return result
    # Find the achievable Fmax with an unreachable target, then close timing at a PLL frequency below it.
    pll(args.probe_mhz, work, args)
    synthesize(work, module, width, args)
    probe = max((place_route(work, args.probe_mhz, s, args) for s in range(1, args.seeds + 1)),
                key=lambda r: r['fmax_mhz'] or 0)
    target = probe['fmax_mhz']
    best = None
    for _ in range(8):
        clock = pll(target, work, args)
        synthesize(work, module, width, args)
        for seed in range(1, args.seeds + 1):
            r = place_route(work, clock, seed, args)
            if r['fmax_mhz'] and r['fmax_mhz'] >= clock:
                best = dict(r, clock_mhz=clock, seed=seed)
                break
        if best:
            break
        target = clock * 0.97
    result['probe'] = probe
    if best:
        run([tool('icepack', args), work / 'top.asc', work / 'euler.bin'])
        result.update(clock_mhz=best['clock_mhz'], fmax_mhz=best['fmax_mhz'], lcs=best['lcs'], brams=best['brams'],
                      seed=best['seed'], time_us=round(cycles / best['clock_mhz'], 3), bitstream=str(work / 'euler.bin'))
        print(f'p{n}: {best["clock_mhz"]} MHz (Fmax {best["fmax_mhz"]}), {best["lcs"]} LCs, {best["brams"]} BRAMs, '
              f'{result["time_us"]} us', flush=True)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('problems', nargs='*', type=int, help='problem numbers (default: all)')
    p.add_argument('--eda', default=os.environ.get('HDLEAN_EDA'), help='directory with yosys, nextpnr-ice40, icepll, icepack, verilator')
    p.add_argument('--seeds', type=int, default=3)
    p.add_argument('--probe-mhz', type=float, default=250.0)
    p.add_argument('--no-pnr', action='store_true')
    p.add_argument('--no-lean-sim', action='store_true')
    args = p.parse_args()
    problems = args.problems or [q['number'] for q in json.loads(run([CLI, 'euler-list']))]
    report_path = ROOT / 'build/euler/report.json'
    for n in problems:
        result = measure(n, args)
        # re-read before writing: several measurements may run side by side
        report = json.loads(report_path.read_text()) if report_path.exists() else {}
        report[str(n)] = result
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
