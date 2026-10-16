#!/usr/bin/env python3
"""Cross-check native domain modules and real two-flop wiring with independent tools."""
import argparse
import json
import os
from pathlib import Path
import subprocess
from check_backends import ROOT, run


def bench(rows, rtlil=False):
    local = [f'dut.local_{d}.reg_0' if rtlil else f'dut.local_{d}.s_0' for d in range(2)]
    registers = [*local,'dut.first_0_0','dut.second_0_0','dut.first_1_0','dut.second_1_0']
    lines = ['module tb;', 'reg clk_0,clk_1,reset_0,reset_1;',
             'reg [1:0] in_0,in_1;', 'wire [1:0] out_0,out_1;',
             'hd_top dut(.*);', 'wire [5:0] storage = {'+', '.join(reversed(registers))+'};',
             'initial begin', 'clk_0=0; clk_1=0;']
    lines += [f"{name}=1'b{int(value)};" for name,value in zip(registers,rows[0]['state'])]
    for cycle,row in enumerate(rows):
        lines += [f"in_0=2'd{int(row['input'][0])}; in_1=2'd{int(row['input'][1])};",
                  f"reset_0={int(row['reset'][0])}; reset_1={int(row['reset'][1])}; #1;",
                  f"if (out_0 !== 2'd{int(row['output'][0])} || out_1 !== 2'd{int(row['output'][1])}) $fatal(1,\"output event {cycle}\");",
                  f"clk_0={int(row['edge'][0])}; clk_1={int(row['edge'][1])}; #1;"]
        value = sum(int(bit)<<k for k,bit in enumerate(row['next']))
        lines += [f"if (storage !== 6'd{value}) $fatal(1,\"storage event {cycle}: %b\",storage);",
                  'clk_0=0; clk_1=0; #1;']
    return '\n'.join(lines+['$display("PASS"); $finish;','end','endmodule'])+'\n'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lake',default=os.environ.get('LAKE','lake'))
    p.add_argument('--iverilog',default=os.environ.get('IVERILOG','iverilog'))
    p.add_argument('--vvp',default=os.environ.get('VVP','vvp'))
    p.add_argument('--yosys',default=os.environ.get('YOSYS','yosys'))
    p.add_argument('--ivl-base',default=os.environ.get('IVL_BASE'))
    a=p.parse_args()
    run([a.lake,'env','lean','--run','Tests/NativeMain.lean'],cwd=ROOT)
    work=ROOT/'build/native-clocks'
    rows=json.loads((work/'trace.json').read_text())
    log=run([a.yosys,'-Q','-T','-p','read_rtlil new.il; hierarchy -top hd_top; check -assert; write_json netlist.json; write_verilog from-il.v'],cwd=work)
    (work/'yosys.log').write_text(log)
    top=json.loads((work/'netlist.json').read_text())['modules']['hd_top']
    syncs=[cell for cell in top['cells'].values() if cell['type']=='$sdff']
    assert len(syncs)==4
    for d in range(2):
        for stage in ['first','second']:
            q=top['netnames'][f'{stage}_{d}_0']['bits']
            drivers=[cell for cell in syncs if cell['connections']['Q']==q]
            assert len(drivers)==1
            cell=drivers[0]
            assert cell['connections']['CLK']==top['ports'][f'clk_{d}']['bits']
            assert cell['connections']['SRST']==top['ports'][f'reset_{d}']['bits']
            assert int(cell['parameters']['WIDTH'],2)==1
            assert int(cell['parameters']['CLK_POLARITY'],2)==1
            assert int(cell['parameters']['SRST_POLARITY'],2)==1
            assert int(cell['parameters']['SRST_VALUE'],2)==0
    options=['-B',a.ivl_base] if a.ivl_base else []
    for source,rtlil in [('new.sv',False),('from-il.v',True)]:
        tb=work/('il-tb.sv' if rtlil else 'sv-tb.sv')
        tb.write_text(bench(rows,rtlil))
        binary=work/(source+'.vvp')
        run([a.iverilog,*options,'-g2012','-s','tb','-o',binary,work/source,tb])
        assert 'PASS' in run([a.vvp,binary])
    mutant=work/'wrong-clock.sv'
    mutant.write_text((work/'new.sv').read_text().replace('posedge clk_1','posedge clk_0'))
    binary=work/'wrong-clock.vvp'
    run([a.iverilog,*options,'-g2012','-s','tb','-o',binary,mutant,work/'sv-tb.sv'])
    bad=subprocess.run([a.vvp,str(binary)],text=True,capture_output=True,timeout=60)
    assert bad.returncode!=0 and 'storage event' in bad.stdout
    print('PASS native clocks: SV and RTLIL, 240 independent/coincident/no-edge events, reset/power-up, and wrong-clock rejection')


if __name__=='__main__':
    main()
