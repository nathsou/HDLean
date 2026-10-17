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
    # The proved emitter writes one module, `hd_top`, with `ins`/`outs` buses and
    # state registers `s_k`.
    module = 'hd_top'
    tb = work / f'{name}_tb.sv'
    tb.write_text(testbench(module, rows, buses=True))
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
            q = parsed['netnames']['state']['bits'][k:k+1]
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
            r'^(\s*)connect \\D [^\n]+', lambda m: m.group(1) + "connect \\D 1'0", paths['rtlil'].read_text(),
            count=1, flags=re.M)
        assert count == 1
        mutant.write_text(mutant_text)
        mutant_script = script.replace(f'read_rtlil {paths["rtlil"].name}', f'read_rtlil {mutant.name}')
        mutant_script = mutant_script.replace(f'write_json {name}_il.json', f'write_json {name}_mutant_il.json')
        result = subprocess.run([yosys, '-p', mutant_script], cwd=work, text=True, capture_output=True, timeout=1200)
        (work / f'{name}_mutant.log').write_text(result.stdout + result.stderr)
        assert result.returncode != 0 and 'unproven $equiv' in result.stderr, 'corrupt next-state passed equivalence'
    print(f'PASS {name}: AIGER + 100 Icarus cycles + Yosys RTLIL equivalence')


def rtl_testbench(info, rows, bits_module):
    """Drive the word-level module and the proved bit-level module with the same
    words; both must show the Lean trace's outputs before every clock edge."""
    ins, outs = info['inputs'], info['outputs']
    nbits_in = sum(p['width'] for p in ins)
    nbits_out = sum(p['width'] for p in outs)
    lines = ['module tb;', 'reg clk = 0; reg rst = 0;']
    lines += [f"reg [{p['width']-1}:0] {p['name']};" for p in ins]
    lines += [f"wire [{p['width']-1}:0] {p['name']};" for p in outs]
    ports = ['.clk(clk)', '.rst(rst)'] + [f".{p['name']}({p['name']})" for p in ins + outs]
    lines.append(f"{info['module']} dut({', '.join(ports)});")
    bus_in = ', '.join(['1\'b0', 'rst'] + [p['name'] for p in reversed(ins)])
    lines += [f'wire [{nbits_out}:0] bits_out;',
              f'{bits_module} bits(.clk(clk), .ins({{{bus_in}}}), .outs(bits_out));',
              f"wire [{nbits_out-1}:0] word_out = {{{', '.join(p['name'] for p in reversed(outs))}}};",
              'integer k;', 'initial begin']
    for st in info['state']:
        if st['depth']:
            lines.append(f"for (k = 0; k < {st['depth']}; k = k + 1) dut.{st['path']}[k] = 0;")
        else:
            lines.append(f"dut.{st['path']} = 0;")
    nstate = info['state_bits']
    for k in range(nstate):
        lines.append(f'bits.s_{k} = 1\'b0;')
    for row in rows:
        for p, v in zip(ins, row['inputs']):
            lines.append(f"{p['name']} = {p['width']}'d{v};")
        lines.append(f"rst = 1'b{int(row['rst'])}; #1;")
        expected = 0
        offset = 0
        for p, v in zip(outs, row['outputs']):
            expected |= (v % (1 << p['width'])) << offset
            offset += p['width']
        lines.append(f"if (word_out !== {nbits_out}'d{expected}) $fatal(1, \"word outputs cycle {row['cycle']}: %h\", word_out);")
        lines.append(f"if (bits_out[{nbits_out-1}:0] !== {nbits_out}'d{expected}) $fatal(1, \"bit outputs cycle {row['cycle']}: %h\", bits_out);")
        lines.append('clk = 1; #1; clk = 0; #1;')
    return '\n'.join(lines + ['$display("PASS"); $finish;', 'end', 'endmodule'])


def check_rtl(work, design, width, iverilog, vvp, yosys, ivl_base, cycles=200):
    """Word-level printer: Icarus runs the word SystemVerilog against the Lean
    trace of Design.step, alongside the proved bit-blasted netlist; Yosys must
    elaborate the word-level text, memories and hierarchy included."""
    words = work / f'{design}_words.sv'
    bits = work / f'{design}_bits.sv'
    run([EXE, 'rtl-emit', design, words, width])
    run([EXE, 'emit', design, 'sv', bits, width])
    tracepath = work / f'{design}_words.json'
    run([EXE, 'rtl-trace', design, tracepath, width, cycles, 7])
    info = json.loads(tracepath.read_text())
    metrics = json.loads(run([EXE, 'rtl-metrics', design, width]))
    info['state_bits'] = metrics['blasted_state_bits']
    tb = work / f'{design}_words_tb.sv'
    tb.write_text(rtl_testbench(info, info['rows'], 'hd_top'))
    options = ['-B', ivl_base] if ivl_base else []
    binary = work / f'{design}_words.vvp'
    run([iverilog, *options, '-g2012', '-s', 'tb', '-o', binary, words, bits, tb])
    assert 'PASS' in run([vvp, binary])
    log = run([yosys, '-p', f'read_verilog -sv {words.name}; hierarchy -check -top {info["module"]}; proc; '
               f'memory; flatten; opt; check -assert; stat'], cwd=work)
    (work / f'{design}_words_yosys.log').write_text(log)
    # Word-level RTLIL: Yosys reads it (memories, hierarchy, Yosys cell semantics)
    # and writes Verilog, which must match the same trace.
    il = work / f'{design}_words.il'
    il_v = work / f'{design}_words_il.v'
    run([EXE, 'rtl-emit', design, il, width])
    log = run([yosys, '-p', f'read_rtlil {il.name}; hierarchy -check -top \\{info["module"]}; proc; '
               f'memory_collect; check -assert; write_verilog -noattr {il_v.name}'], cwd=work)
    (work / f'{design}_words_il_yosys.log').write_text(log)
    binary = work / f'{design}_words_il.vvp'
    run([iverilog, *options, '-g2012', '-s', 'tb', '-o', binary, il_v, bits, tb])
    assert 'PASS' in run([vvp, binary])
    print(f'PASS {design}: word SV, word RTLIL (through Yosys) and bit-blasted SV match {cycles} cycles '
          f'of Design.step; Yosys elaborates both word-level texts')


def check_abc(work, design, width, yosys):
    """ABC-optimised emission: the result must be validated by the verified LRAT
    checker, match the trace, and be Yosys-equivalent to the plain emission."""
    name = f'{design}_{width}_abc'
    plain = work / f'{design}_{width}.sv'
    rtlil = work / f'{name}.rtlil'
    aag = work / f'{name}.aiger'
    message = run([EXE, 'abc-emit', design, 'rtlil', rtlil, width])
    assert 'validated' in message, message
    run([EXE, 'abc-emit', design, 'aiger', aag, width])
    rows = json.loads((work / f'{design}_{width}.json').read_text())
    check_aag(aag, rows)
    script = (f'read_verilog -sv {plain.name}; proc; rename hd_top gold; design -stash gold; '
              f'read_rtlil {rtlil.name}; rename hd_top gate; design -stash gate; '
              f'design -copy-from gold -as gold gold; design -copy-from gate -as gate gate; '
              f'splitnets gold/state gate/state; expose -evert-dff -shared; opt_clean; check -assert; '
              f'equiv_make gold gate equiv; hierarchy -top equiv; opt_merge; opt_clean; equiv_simple; '
              f'equiv_induct; equiv_status -assert')
    log = run([yosys, '-p', script], cwd=work)
    assert 'Equivalence successfully proven!' in log
    print(f'PASS {name}: {message.strip()} Trace and Yosys equivalence with the plain emission.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--iverilog', default=os.environ.get('IVERILOG', 'iverilog'))
    parser.add_argument('--vvp', default=os.environ.get('VVP', 'vvp'))
    parser.add_argument('--yosys', default=os.environ.get('YOSYS', 'yosys'))
    parser.add_argument('--ivl-base', default=os.environ.get('IVL_BASE'))
    designs = ['counter', 'fifo', 'pipeline', 'ring', 'ram', 'toy16', 'ops']
    parser.add_argument('--designs', nargs='+', choices=designs, default=designs)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/backend-checks')
    args = parser.parse_args()
    for tool in (args.iverilog, args.vvp, args.yosys):
        if not shutil.which(tool):
            parser.error(f'required external checker is missing: {tool}')
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    # Every design is word-level: its bit-blasted netlist goes through AIGER,
    # Icarus and Yosys equivalence, and its word-level SystemVerilog and RTLIL
    # through Icarus (against the Lean trace) and Yosys.
    widths = {'counter': (8,), 'fifo': (1, 8, 16), 'pipeline': (1, 8), 'ring': (1, 8), 'ram': (1, 8),
              'toy16': (8,), 'ops': (8,)}
    for design in args.designs:
        for width in widths[design]:
            check_design(work, design, width, args.iverilog, args.vvp, args.yosys, args.ivl_base)
        check_rtl(work, design, widths[design][-1], args.iverilog, args.vvp, args.yosys, args.ivl_base)
        if design in ('counter', 'ring', 'ram') and shutil.which(os.environ.get('HDLEAN_ABC', 'yosys-abc')):
            check_abc(work, design, widths[design][-1], args.yosys)



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout)
        print(error.stderr)
        raise
