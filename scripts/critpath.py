#!/usr/bin/env python3
"""Summarise nextpnr's critical path: logic levels, carry-chain lengths, routing."""
import re, sys
text = open(sys.argv[1]).read()
blocks = text.split('Critical path report for clock')
if len(blocks) < 2: sys.exit('no critical path')
clock = sys.argv[2] if len(sys.argv) > 2 else 'fclk'
paths = [b for b in blocks[1:] if b.lstrip().startswith("'" + clock)]
path = paths[-1] if paths else blocks[-1]
rows = re.findall(r'Info:\s+(clk-to-q|logic|routing|setup)\s+([\d.]+)\s+([\d.]+)\s+(Source|Sink)\s+(\S+)', path)
carry = 0
for kind, d, cum, role, name in rows:
    short = re.sub(r'(_SB_CARRY_C[IO]_C[IO])+', '_<carry>', name)
    short = short[:110]
    if kind == 'logic' and 'COUT' in name and 'CIN' not in name:
        pass
    if kind == 'logic' and name.endswith('COUT'):
        carry += 1
        continue
    if carry:
        print(f'          ... {carry} carry stages')
        carry = 0
    print(f'{kind:9} {d:>5} {cum:>6} {role:6} {short}')
    if kind == 'setup': break
