"""Native independent clocks, arbitrary startup, and explicit event AIGER checks."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_backends import check_aag

LAKE = os.environ.get('LAKE', 'lake')
IVERILOG = os.environ.get('IVERILOG', 'iverilog')
VVP = os.environ.get('VVP', 'vvp')
YOSYS = os.environ.get('YOSYS', 'yosys')


def run(args, cwd=ROOT):
    result = subprocess.run(list(map(str, args)), cwd=cwd, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise AssertionError(f'{args[0]} failed:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def bench(rows):
    ni, no = len(rows[0]['inputs']), len(rows[0]['outputs'])
    lines = ['module tb;', 'reg [1:0] clocks;', f'reg [{ni-1}:0] inputs;', f'wire [{no-1}:0] outputs;']
    ports = [f'.clk_{k}(clocks[{k}])' for k in range(2)]
    ports += [f'.in_{k}(inputs[{k}])' for k in range(ni)]
    ports += [f'.out_{k}(outputs[{k}])' for k in range(no)]
    lines += [f'hd_async_fifo_2x4 dut({", ".join(ports)});', 'initial begin', 'clocks = 0;']
    for k, b in enumerate(rows[0]['state']):
        lines.append(f'dut.n{ni+k+1} = 1\'b{int(b)};')
    for row in rows:
        bits = lambda xs: sum(int(b) << k for k, b in enumerate(xs))
        lines += [f'inputs = {ni}\'d{bits(row["inputs"])}; #1;',
                  f'if (outputs !== {no}\'d{bits(row["outputs"])}) $fatal(1, "output event {row["cycle"]}");',
                  f'clocks = 2\'d{bits(row["edges"])}; #1;']
        for k, b in enumerate(row['next']):
            lines.append(f'if (dut.n{ni+k+1} !== 1\'b{int(b)}) $fatal(1, "state event {row["cycle"]} bit {k}");')
        lines += ['clocks = 0; #1;']
    return '\n'.join(lines + ['$display("PASS"); $finish;', 'end', 'endmodule'])


@unittest.skipUnless(all(shutil.which(x) for x in [LAKE, IVERILOG, VVP, YOSYS]),
                     'Lean, Icarus and Yosys are required for native multi-clock checks')
class MultiClockTests(unittest.TestCase):
    def test_async_physical_clocks_and_event_aiger(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'work') as tmp:
            folder = Path(tmp)
            run([LAKE, 'env', 'lean', '--run', 'Tests/independent/AsyncHardware.lean', folder])
            rows = json.loads((folder / 'trace.json').read_text())
            clocks = json.loads((folder / 'clocks.json').read_text())
            self.assertEqual({tuple(row['edges']) for row in rows}, {(False, False), (False, True), (True, False), (True, True)})
            event_rows = [dict(row, inputs=row['inputs'] + row['edges'] + [False]) for row in rows]
            check_aag(folder / 'async.aiger', event_rows)
            (folder / 'tb.sv').write_text(bench(rows))
            ivl_options = ['-B', os.environ['IVL_BASE']] if os.environ.get('IVL_BASE') else []
            run([IVERILOG, *ivl_options, '-g2012', '-s', 'tb', '-o', folder / 'sim.vvp', folder / 'async.sv', folder / 'tb.sv'])
            self.assertIn('PASS', run([VVP, folder / 'sim.vvp']))
            script = ('read_verilog -sv async.sv; proc; write_json sv.json; '
                      'rename hd_async_fifo_2x4 gold; design -stash gold; '
                      'read_rtlil async.rtlil; write_json il.json; rename hd_async_fifo_2x4 gate; '
                      'design -stash gate; design -copy-from gold -as gold gold; '
                      'design -copy-from gate -as gate gate; expose -evert-dff -shared; '
                      'opt_clean; select -assert-none t:$dff; check -assert; equiv_make gold gate equiv; '
                      'hierarchy -top equiv; equiv_simple; equiv_status -assert')
            self.assertIn('Equivalence successfully proven!', run([YOSYS, '-p', script], cwd=folder))
            # Clock wiring and polarity are checked before eversion removes flops.
            for suffix in ['sv', 'il']:
                module = json.loads((folder / f'{suffix}.json').read_text())['modules']['hd_async_fifo_2x4']
                cells = list(module['cells'].values())
                self.assertTrue(all(c['type'] in ('$dff', '$and', '$not') for c in cells))
                regs = [c for c in cells if c['type'] == '$dff']
                self.assertEqual(len(regs), len(clocks))
                for k, domain in enumerate(clocks):
                    q = module['netnames'][f'n{len(rows[0]["inputs"])+k+1}']['bits']
                    drivers = [c for c in regs if c['connections']['Q'] == q]
                    self.assertEqual(len(drivers), 1)
                    self.assertEqual(int(drivers[0]['parameters']['CLK_POLARITY'], 2), 1)
                    self.assertEqual(drivers[0]['connections']['CLK'], module['ports'][f'clk_{domain}']['bits'])


if __name__ == '__main__':
    unittest.main()
