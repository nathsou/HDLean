#!/usr/bin/env python3
"""Print the Markdown results table of docs/Euler.md from build/euler/report.json."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
report = json.loads((ROOT / 'build/euler/report.json').read_text())
print('| Problem | Answer | Cycles | Clock (MHz) | Time | Logic cells | Block RAMs |')
print('|---|---:|---:|---:|---:|---:|---:|')
for key in sorted(report, key=int):
    r = report[key]
    if 'clock_mhz' not in r:
        continue
    t = r['time_us']
    time = f'{t / 1000:.2f} ms' if t >= 1000 else f'{t:.2f} µs'
    print(f"| {r['number']}. {r['title']} | {r['answer']} | {r['cycles']:,} | {r['clock_mhz']:.1f} | {time} | "
          f"{r['lcs']:,} | {r['brams']} |")
