#!/usr/bin/env python3
"""Cross-check the multi-clock word-level printers with independent tools.

The dual-clock FIFO (`async`) is emitted as word-level SystemVerilog and RTLIL
(each read back by the proved parser in the CLI). Icarus runs the SystemVerilog,
and the Verilog Yosys writes from the RTLIL, with real clocks, two-flop
synchronizers and the shared memory, against the Lean trace of `MDesign.next`.
Synchronizers sample the old source value, which is what an event simulator does
when two clock edges coincide and what it does trivially otherwise.
"""
import argparse
import json
import os
import shutil
from check_backends import ROOT, EXE, run


def testbench(info):
    doms = info['domains']
    lines = ['module tb;']
    ports = []
    for d, dom in enumerate(doms):
        lines += [f'reg clk_{d} = 0;', f'reg rst_{d} = 0;']
        ports += [f'.clk_{d}(clk_{d})', f'.rst_{d}(rst_{d})']
        for k, w in enumerate(dom['inputs']):
            lines.append(f'reg [{w-1}:0] x_{d}_{k+1} = 0;')
            ports.append(f'.x_{d}_{k+1}(x_{d}_{k+1})')
        for k, w in enumerate(dom['outputs']):
            lines.append(f'wire [{w-1}:0] y_{d}_{k};')
            ports.append(f'.y_{d}_{k}(y_{d}_{k})')
    lines += [f'{info["module"]} dut({", ".join(ports)});', 'integer i;', 'initial begin']
    # The trace starts from all-zero memories (the registers are reset on step 0).
    for m, depth in enumerate(info['memories']):
        lines.append(f'for (i = 0; i < {depth}; i = i + 1) dut.sm_{m}[i] = 0;')
    for step, row in enumerate(info['rows']):
        for d, dom in enumerate(doms):
            for k, v in enumerate(row['inputs'][d]):
                lines.append(f"x_{d}_{k+1} = {dom['inputs'][k]}'d{v};")
            lines.append(f"rst_{d} = 1'b{int(row['resets'][d])};")
        lines.append('#1;')
        if step > 0:
            for d, dom in enumerate(doms):
                for k, v in enumerate(row['outputs'][d]):
                    w = dom['outputs'][k]
                    check = f"y_{d}_{k} !== {w}'d{v}"
                    lines.append(f'if ({check}) $fatal(1, "step {step}: y_{d}_{k} = %d, expected {v}", y_{d}_{k});')
        lines.append(' '.join(f"clk_{d} = 1'b{int(e)};" for d, e in enumerate(row['edges'])) + ' #1;')
        lines.append(' '.join(f'clk_{d} = 0;' for d in range(len(doms))) + ' #1;')
    return '\n'.join(lines + ['$display("PASS"); $finish;', 'end', 'endmodule']) + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    p.add_argument('--iverilog', default=os.environ.get('IVERILOG', 'iverilog'))
    p.add_argument('--vvp', default=os.environ.get('VVP', 'vvp'))
    p.add_argument('--yosys', default=os.environ.get('YOSYS', 'yosys'))
    p.add_argument('--ivl-base', default=os.environ.get('IVL_BASE'))
    a = p.parse_args()
    for tool in (a.iverilog, a.vvp, a.yosys):
        if not shutil.which(tool):
            p.error(f'required external checker is missing: {tool}')
    work = ROOT / 'build/native-clocks'
    work.mkdir(parents=True, exist_ok=True)
    options = ['-B', a.ivl_base] if a.ivl_base else []
    for width in (1, 8):
        sv, il, il_v = work / f'async_{width}.sv', work / f'async_{width}.il', work / f'async_{width}_il.v'
        run([EXE, 'rtl-emit', 'async', sv, width])
        run([EXE, 'rtl-emit', 'async', il, width])
        for seed in (1, 42):
            trace = work / f'async_{width}_{seed}.json'
            run([EXE, 'rtl-trace', 'async', trace, width, 400, seed])
            info = json.loads(trace.read_text())
            tb = work / f'async_{width}_{seed}_tb.sv'
            tb.write_text(testbench(info))
            binary = work / f'async_{width}_{seed}.vvp'
            run([a.iverilog, *options, '-g2012', '-s', 'tb', '-o', binary, sv, tb])
            assert 'PASS' in run([a.vvp, binary])
            log = run([a.yosys, '-p', f'read_rtlil {il.name}; hierarchy -check -top \\hd_mtop; proc; '
                       f'memory_collect; check -assert; write_verilog -noattr {il_v.name}'], cwd=work)
            (work / f'async_{width}_il_yosys.log').write_text(log)
            binary = work / f'async_{width}_{seed}_il.vvp'
            run([a.iverilog, *options, '-g2012', '-s', 'tb', '-o', binary, il_v, tb])
            assert 'PASS' in run([a.vvp, binary])
        log = run([a.yosys, '-p', f'read_verilog -sv {sv.name}; hierarchy -check -top hd_mtop; proc; '
                   f'memory; flatten; opt; check -assert; stat'], cwd=work)
        (work / f'async_{width}_yosys.log').write_text(log)
        print(f'PASS async w={width}: word SV and word RTLIL (through Yosys) match 2 x 400 steps of MDesign.next '
              'with two clocks; Yosys elaborates the SystemVerilog')


if __name__ == '__main__':
    main()
