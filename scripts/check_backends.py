#!/usr/bin/env python3
"""Cross-check independent AIGER interpretation, Icarus simulation, and Yosys RTLIL.

External tools validate printers; these checks are not a theorem about every design.
"""
import argparse
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile

if not __debug__:
    raise SystemExit('Backend verification requires Python assertions; disable optimization.')

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/hdlean'


def run(args, **kwargs):
    return subprocess.run([str(x) for x in args], check=True, text=True, capture_output=True,
                          timeout=1200, **kwargs).stdout


def read_aag(path):
    lines = path.read_text().splitlines()
    header = lines.pop(0).split()
    assert header[0] == 'aag' and len(header) == 6
    maximum, inputs, latches, outputs, gates = map(int, header[1:])
    assert maximum == inputs + latches + gates
    ins = [int(lines.pop(0)) for _ in range(inputs)]
    regs = [tuple(map(int, lines.pop(0).split())) for _ in range(latches)]
    outs = [int(lines.pop(0)) for _ in range(outputs)]
    ands = [tuple(map(int, lines.pop(0).split())) for _ in range(gates)]
    assert ins == [2 * (k + 1) for k in range(inputs)]
    assert all(cur == init for cur, _, init in regs), 'power-up was initialized'
    for offset, (lhs, a, b) in enumerate(ands):
        assert lhs == 2 * (inputs + latches + offset + 1)
        assert lhs > a >= 0 and lhs > b >= 0
    return inputs, regs, outs, ands


def check_aag(path, rows):
    inputs, regs, outs, gates = read_aag(path)
    for row in rows:
        values = [False] + row['inputs'] + row['state']
        def lit(l):
            return values[l // 2] ^ bool(l % 2)
        assert len(row['inputs']) == inputs
        for lhs, a, b in gates:
            assert lhs // 2 == len(values)
            values.append(lit(a) and lit(b))
        assert [lit(n) for _, n, _ in regs] == row['next'], row['cycle']
        assert [lit(o) for o in outs] == row['outputs'], row['cycle']


def testbench(module, rows, buses=False):
    ni, nr, no = len(rows[0]['inputs']), len(rows[0]['state']), len(rows[0]['outputs'])
    lines = ['module tb;', 'reg clk;', f'reg [{ni-1}:0] inputs;', f'wire [{no-1}:0] outputs;']
    ports = (['.clk(clk)', ".ins({1'b0,inputs})",'.outs(outputs_padded)'] if buses else
             ['.clk(clk)'] + [f'.in_{k}(inputs[{k}])' for k in range(ni)] + [f'.out_{k}(outputs[{k}])' for k in range(no)])
    if buses:
        lines += [f'wire [{no}:0] outputs_padded;',f'assign outputs = outputs_padded[{no-1}:0];']
    lines += [f'{module} dut({", ".join(ports)});']
    if nr:
        packed = ', '.join((f'dut.s_{k}' if buses else f'dut.n{ni+k+1}') for k in reversed(range(nr)))
        lines += [f'wire [{nr-1}:0] state_bits = {{{packed}}};']
    lines += ['initial begin', 'clk = 0;']
    for k, b in enumerate(rows[0]['state']):
        target = f'dut.s_{k}' if buses else f'dut.n{ni+k+1}'
        lines.append(f'{target} = 1\'b{int(b)};')
    for row in rows:
        v = sum(int(b) << k for k, b in enumerate(row['inputs']))
        out = sum(int(b) << k for k, b in enumerate(row['outputs']))
        lines += [f'inputs = {ni}\'d{v}; #1;',
                  f'if (outputs !== {no}\'d{out}) $fatal(1, "outputs cycle {row["cycle"]}: %b", outputs);',
                  'clk = 1; #1;']
        if nr:
            expected = sum(int(b) << k for k,b in enumerate(row['next']))
            lines.append(f'if (state_bits !== {nr}\'d{expected}) $fatal(1, "state cycle {row["cycle"]}: %b", state_bits);')
        lines += ['clk = 0; #1;']
    return '\n'.join(lines + ['$display("PASS"); $finish;', 'end', 'endmodule'])


def check_design(work, design, width, iverilog, vvp, yosys, ivl_base):
    name = f'{design}_{width}'
    paths = {fmt: work / f'{name}.{fmt}' for fmt in ('sv', 'aiger', 'rtlil')}
    for fmt, path in paths.items():
        run([EXE, 'emit', design, fmt, path, width])
    tracepath = work / f'{name}.json'
    run([EXE, 'trace', design, tracepath, width, 100, 42])
    rows = json.loads(tracepath.read_text())
    check_aag(paths['aiger'], rows)
    module = {'fifo': f'hd_fifo2_w{width}', 'counter': 'hd_decade',
              'pipeline': f'hd_pipeline3_w{width}', 'ram': f'hd_ram_16x{width}', 'ring':f'hd_fifo_ring_d16_w{width}', 'toy16':'hd_top'}[design]
    tb = work / f'{name}_tb.sv'
    tb.write_text(testbench(module, rows, buses=(design == 'toy16')))
    options = ['-B', ivl_base] if ivl_base else []
    binary = work / f'{name}.vvp'
    run([iverilog, *options, '-g2012', '-s', 'tb', '-o', binary, paths['sv'], tb])
    assert 'PASS' in run([vvp, binary])
    # Expose each matched physical register as an arbitrary-state input and its
    # D/clock pins as outputs. This proves the complete combinational transition
    # relation and avoids version-dependent assumptions about uninitialized flops.
    ni, nr = len(rows[0]['inputs']), len(rows[0]['state'])
    script = (f'read_verilog -sv {paths["sv"].name}; proc; write_json {name}_sv.json; '
              f'rename {module} gold; design -stash gold; '
              f'read_rtlil {paths["rtlil"].name}; write_json {name}_il.json; '
              f'rename {module} gate; design -stash gate; design -copy-from gold -as gold gold; '
              f'design -copy-from gate -as gate gate; splitnets gold/state gate/state; expose -evert-dff -shared; '
              f'opt_clean; select -assert-none t:$dff; check -assert; equiv_make gold gate equiv; '
              f'hierarchy -top equiv; opt_merge; opt_clean; equiv_simple; equiv_status -assert; stat')
    log = run([yosys, '-p', script], cwd=work)
    (work / f'{name}_yosys.log').write_text(log)
    assert 'Equivalence successfully proven!' in log
    # Eversion alone would erase edge polarity. Audit the original parsed cells
    # so a wrong-edge, extra-state, latch, or wrong-clock printer is also rejected.
    for suffix in ('sv', 'il'):
        parsed = json.loads((work / f'{name}_{suffix}.json').read_text())['modules'][module]
        registers = [c for c in parsed['cells'].values() if c['type'] == '$dff']
        assert len(registers) == nr
        assert all(c['type'] in ('$dff', '$and', '$not') for c in parsed['cells'].values())
        for k in range(nr):
            q = (parsed['netnames']['state']['bits'][k:k+1] if design == 'toy16' else
                 parsed['netnames'][f'n{ni + k + 1}']['bits'])
            drivers = [c for c in registers if c['connections']['Q'] == q]
            assert len(drivers) == 1, f'state bit {k} has no unique driver'
            cell = drivers[0]
            assert int(cell['parameters']['WIDTH'], 2) == 1
            assert int(cell['parameters']['CLK_POLARITY'], 2) == 1
            assert cell['connections']['CLK'] == parsed['ports']['clk']['bits']
    if design == 'counter':
        # An intentionally corrupted next-state assignment must be refuted. This
        # guards against accidentally checking only combinational output aliases.
        mutant = work / f'{name}_mutant.rtlil'
        mutant_text, count = re.subn(
            r'    connect \\D [^\n]+', lambda _: "    connect \\D 1'0", paths['rtlil'].read_text(), count=1)
        assert count == 1
        mutant.write_text(mutant_text)
        mutant_script = script.replace(f'read_rtlil {paths["rtlil"].name}', f'read_rtlil {mutant.name}')
        mutant_script = mutant_script.replace(f'write_json {name}_il.json', f'write_json {name}_mutant_il.json')
        result = subprocess.run([yosys, '-p', mutant_script], cwd=work, text=True, capture_output=True, timeout=1200)
        (work / f'{name}_mutant.log').write_text(result.stdout + result.stderr)
        assert result.returncode != 0 and 'unproven $equiv' in result.stderr, 'corrupt next-state passed equivalence'
    print(f'PASS {name}: AIGER + 100 Icarus cycles + Yosys RTLIL equivalence')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--iverilog', default=os.environ.get('IVERILOG', 'iverilog'))
    parser.add_argument('--vvp', default=os.environ.get('VVP', 'vvp'))
    parser.add_argument('--yosys', default=os.environ.get('YOSYS', 'yosys'))
    parser.add_argument('--ivl-base', default=os.environ.get('IVL_BASE'))
    parser.add_argument('--designs', nargs='+', choices=['fifo','counter','pipeline','ram','ring','toy16'],
                        default=['fifo','counter','pipeline','ram','ring','toy16'])
    parser.add_argument('--output', type=Path, default=ROOT / 'build/backend-checks')
    args = parser.parse_args()
    for tool in (args.iverilog, args.vvp, args.yosys):
        if not shutil.which(tool):
            parser.error(f'required external checker is missing: {tool}')
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    widths = {'fifo':(0,1,8,16), 'counter':(8,), 'pipeline':(1,8),
              'ram':(1,8), 'ring':(1,8), 'toy16':(8,)}
    for design in args.designs:
        for width in widths[design]:
            check_design(work, design, width, args.iverilog, args.vvp, args.yosys, args.ivl_base)



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout)
        print(error.stderr)
        raise
