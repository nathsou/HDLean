#!/usr/bin/env python3
"""Render HDLean trace JSON as a table or VCD (pre-edge values at even ticks)."""
import argparse
import json
from pathlib import Path


def word(bits):
    return ''.join('1' if bit else '0' for bit in reversed(bits)) or '0'


def render(rows, fmt):
    if fmt == 'table':
        return '\n'.join(['cycle | inputs | state | outputs | next', '--- | --- | --- | --- | ---'] +
            [f'{r["cycle"]} | {word(r["inputs"])} | {word(r["state"])} | {word(r["outputs"])} | {word(r["next"])}' for r in rows]) + '\n'
    if not rows:
        raise ValueError('VCD requires a nonempty trace')
    names = ('inputs', 'state', 'outputs', 'next')
    lines = ['$timescale 1ns $end', '$scope module hdlean $end']
    for ident, name in zip('abcd', names):
        lines.append(f'$var wire {max(1, len(rows[0][name]))} {ident} {name} $end')
    lines += ['$upscope $end', '$enddefinitions $end']
    for r in rows:
        lines.append(f'#{2*r["cycle"]}')
        lines.extend(f'b{word(r[name])} {ident}' for ident, name in zip('abcd', names))
    return '\n'.join(lines) + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('trace', type=Path)
    p.add_argument('--format', choices=['table', 'vcd'], default='table')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    text = render(json.loads(a.trace.read_text()), a.format)
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
