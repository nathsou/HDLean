#!/usr/bin/env python3
"""Render HDLean trace JSON as a table or VCD (pre-edge values at even ticks)."""
import argparse
import json
import re
from pathlib import Path


def word(bits):
    return ''.join('1' if bit else '0' for bit in reversed(bits)) or '0'


def render(rows, fmt, selected=None):
    metadata = (rows[0].get('signals') or {}) if rows else {}
    channels = ('inputs', 'state', 'outputs', 'next')
    fields = {}
    for channel in channels:
        for k, name in enumerate(metadata.get(channel, [])):
            fields[f'{channel}.{name}'] = (channel, k)
    if selected:
        missing = set(selected) - fields.keys()
        if missing:
            raise ValueError(f'unknown named signals: {sorted(missing)}')
        if fmt == 'table':
            return '\n'.join(['cycle | ' + ' | '.join(selected), '--- | ' + ' | '.join('---' for _ in selected)] +
                [str(r['cycle']) + ' | ' + ' | '.join(str(int(r[fields[s][0]][fields[s][1]])) for s in selected)
                 for r in rows]) + '\n'
    if fmt == 'table':
        return '\n'.join(['cycle | inputs | state | outputs | next', '--- | --- | --- | --- | ---'] +
            [f'{r["cycle"]} | {word(r["inputs"])} | {word(r["state"])} | {word(r["outputs"])} | {word(r["next"])}' for r in rows]) + '\n'
    if not rows:
        raise ValueError('VCD requires a nonempty trace')
    names = channels
    lines = ['$timescale 1ns $end', '$scope module hdlean $end']
    for ident, name in zip('abcd', names):
        lines.append(f'$var wire {max(1, len(rows[0][name]))} {ident} {name} $end')
    named = list(selected) if selected else list(fields)
    for k, name in enumerate(named):
        identifier = re.sub(r'[^A-Za-z0-9_$]', '_', name)
        lines.append(f'$var wire 1 s{k} {identifier}_{k} $end')
    lines += ['$upscope $end', '$enddefinitions $end']
    for r in rows:
        lines.append(f'#{2*r["cycle"]}')
        lines.extend(f'b{word(r[name])} {ident}' for ident, name in zip('abcd', names))
        lines.extend(f'{int(r[fields[name][0]][fields[name][1]])}s{k}' for k, name in enumerate(named))
    return '\n'.join(lines) + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('trace', type=Path)
    p.add_argument('--format', choices=['table', 'vcd'], default='table')
    p.add_argument('--output', type=Path)
    p.add_argument('--signals', nargs='+', help='select named bits, such as state.count_0 or inputs.rst')
    a = p.parse_args()
    text = render(json.loads(a.trace.read_text()), a.format, a.signals)
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
