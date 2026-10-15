#!/usr/bin/env python3
"""Generate kernel proofs for exact ASCII artifact bytes and an explicit graph candidate.

The generator is untrusted: graph validation, lexical normalization and parsing are
all proved by Lean. A release comparator must bind the input artifact and generated
source hashes in the returned manifest, and replay text_correct independently.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

FORMATS = {'aiger': 'aiger', 'sv': 'systemVerilog', 'rtlil': 'rtlil'}
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def array(xs):
    xs = list(xs)
    if len(xs) <= 256:
        return '#[' + ', '.join(map(str, xs)) + ']'
    chunks = ['[' + ', '.join(map(str, xs[i:i + 128])) + ']' for i in range(0, len(xs), 128)]
    return '(List.flatten [' + ', '.join(chunks) + ']).toArray'


def graph_from_aiger(data):
    """An untrusted candidate decoder; the generated theorem checks every graph cone."""
    lines = iter(data.decode('ascii').splitlines())
    header = next(lines).split()
    if len(header) != 6 or header[0] != 'aag':
        raise ValueError('expected ASCII AIGER header')
    m, ni, nr, no, ng = map(int, header[1:])
    if min(m, ni, nr, no, ng) < 0 or m != ni + nr + ng:
        raise ValueError('invalid AIGER dimensions')
    for k in range(ni):
        if int(next(lines)) != 2 * (k + 1):
            raise ValueError('noncanonical AIGER input')
    ns = []
    for k in range(nr):
        lhs, nxt, init = map(int, next(lines).split())
        if lhs != 2 * (ni + k + 1) or init != lhs or nxt < 0:
            raise ValueError('expected arbitrary-power-up AIGER latch')
        ns.append(nxt)
    outputs = [int(next(lines)) for _ in range(no)]
    gates = []
    for k in range(ng):
        lhs, a, b = map(int, next(lines).split())
        if lhs != 2 * (ni + nr + k + 1) or min(a, b) < 0:
            raise ValueError('noncanonical AIGER gate')
        gates.append(f'⟨{lhs // 2}, {a}, {b}⟩')
    if any(x < 0 for x in outputs):
        raise ValueError('negative literal')
    return (f'⟨"candidate", {ni}, {nr}, {array(gates)}, {array(ns)}, {array(outputs)}, '
            f'Array.replicate {ni} "", Array.replicate {nr} "", '
            f'Array.replicate {no} "", Array.replicate {nr} ""⟩')


def encode_lines(lines):
    out = []
    unique_lines = list(dict.fromkeys(lines))
    line_indices = {line: i for i, line in enumerate(unique_lines)}
    for i, line in enumerate(unique_lines):
        token = line.strip(b' \t\r')
        norm = '[' + ', '.join(map(str, token)) + ']'
        out.extend([
            f'private def byteLine{i} : List UInt8 := [{", ".join(map(str, line))}]',
            f'private theorem byteLine{i}_ascii : byteLine{i}.all (fun b => decide (b.toNat < 128)) = true := by decide +kernel',
            f'private theorem byteLine{i}_noNL : byteLine{i}.all (fun b => b.toNat != 10) = true := by decide +kernel',
            f'private def tokenLine{i} : List Nat := {norm}',
            f'private theorem byteLine{i}_normalized : Format.normalizeByteLines [byteLine{i}] = {"[tokenLine" + str(i) + "]" if token else "[]"} := by decide +kernel'])
    names = ', '.join(f'byteLine{line_indices[line]}' for line in lines)
    out.append(f'private def rawLines : List (List UInt8) := [{names}]')
    ascii_lemmas = ', '.join(f'byteLine{i}_ascii' for i in range(len(unique_lines)))
    noNL_lemmas = ', '.join(f'byteLine{i}_noNL' for i in range(len(unique_lines)))
    norm_lemmas = ', '.join(f'byteLine{i}_normalized' for i in range(len(unique_lines)))
    token_names = ', '.join(f'tokenLine{line_indices[l]}' for l in lines if l.strip(b' \t\r'))
    out.extend([
        f'''private theorem lines_ascii : (rawLines.flatMap (fun l => l ++ [10])).all
    (fun b => decide (b.toNat < 128)) = true := by
  simp only [rawLines, List.all_flatMap, List.all_append, List.all_cons, List.all_nil,
    {ascii_lemmas}, Bool.true_and]
  all_goals decide +kernel''',
        f'''private theorem lines_noNL : rawLines.all (fun l => l.all (fun b => b.toNat != 10)) = true := by
  simp only [rawLines, List.all_cons, List.all_nil, {noNL_lemmas}, Bool.true_and]''',
        f'private def tokens : List (List Nat) := [{token_names}]',
        f'''private theorem lines_normalized : Format.normalizeByteLines rawLines = tokens := by
  simp only [rawLines, normalize_cons, {norm_lemmas}, List.singleton_append, List.nil_append]
  rfl'''])
    return out


def encode_chunks(lines, size=64):
    """Bound environment overhead for large files with compositional chunk proofs."""
    chunks = [lines[i:i + size] for i in range(0, len(lines), size)]
    out = ['''private theorem normalize_append (a b : List (List UInt8)) :
    Format.normalizeByteLines (a ++ b) = Format.normalizeByteLines a ++ Format.normalizeByteLines b := by
  simp only [Format.normalizeByteLines, List.map_append, List.filter_append]''']
    for i, chunk in enumerate(chunks):
        raw = '[' + ', '.join('[' + ', '.join(map(str, line)) + ']' for line in chunk) + ']'
        tokens = [line.strip(b' \t\r') for line in chunk]
        norm = '[' + ', '.join('[' + ', '.join(map(str, line)) + ']' for line in tokens if line) + ']'
        out.extend([
            f'private def rawChunk{i} : List (List UInt8) := {raw}',
            f'private theorem chunk{i}_ascii : (rawChunk{i}.flatMap (fun l => l ++ [10])).all (fun b => decide (b.toNat < 128)) = true := by decide +kernel',
            f'private theorem chunk{i}_noNL : rawChunk{i}.all (fun l => l.all (fun b => b.toNat != 10)) = true := by decide +kernel',
            f'private def tokenChunk{i} : List (List Nat) := {norm}',
            f'private theorem chunk{i}_normalized : Format.normalizeByteLines rawChunk{i} = tokenChunk{i} := by decide +kernel',
        ])
    raw_names = ', '.join(f'rawChunk{i}' for i in range(len(chunks)))
    token_names = ', '.join(f'tokenChunk{i}' for i in range(len(chunks)))
    ascii_lemmas = ', '.join(f'chunk{i}_ascii' for i in range(len(chunks)))
    noNL_lemmas = ', '.join(f'chunk{i}_noNL' for i in range(len(chunks)))
    norm_lemmas = ', '.join(f'chunk{i}_normalized' for i in range(len(chunks)))
    out.extend([
        f'private def rawLines : List (List UInt8) := [{raw_names}].flatten',
        f'private def tokens : List (List Nat) := [{token_names}].flatten',
        f'''private theorem lines_ascii : (rawLines.flatMap (fun l => l ++ [10])).all
    (fun b => decide (b.toNat < 128)) = true := by
  simp only [rawLines, List.flatten_cons, List.flatten_nil, List.flatMap_append, List.flatMap_nil,
    List.all_append, List.all_nil, {ascii_lemmas}, Bool.true_and]''',
        f'''private theorem lines_noNL : rawLines.all (fun l => l.all (fun b => b.toNat != 10)) = true := by
  simp only [rawLines, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, {noNL_lemmas}, Bool.true_and]''',
        f'''private theorem lines_normalized : Format.normalizeByteLines rawLines = tokens := by
  simp only [rawLines, tokens, List.flatten_cons, List.flatten_nil, normalize_append, {norm_lemmas}]
  rfl''',
    ])
    return out


def generate(artifact, graph_aiger, design, width, format, namespace):
    if not IDENTIFIER.fullmatch(namespace):
        raise ValueError('invalid Lean namespace')
    if design not in ('counter', 'fifo', 'pipeline', 'ram', 'toy16', 'circular', 'ring') or type(width) is not int or not 0 <= width <= 64:
        raise ValueError('unsupported design or width')
    if not artifact or any(b >= 128 for b in artifact) or not artifact.endswith(b'\n'):
        raise ValueError('certificate requires nonempty ASCII bytes ending in LF')
    circuit, modules = {
        'counter': ('Counter.hardware', ['Designs.Counter.Impl']),
        'fifo': (f'(Fifo.hardware {width})', ['Designs.Fifo.Impl']),
        'pipeline': (f'(SkidBuffer.hardware {width})', ['Designs.SkidBuffer.Hardware']),
        'ram': (f'(RAMCircuit.hardware 4 {width})', ['HDLean.Lib.MemoryCircuit']),
        'toy16': ('(Toy16.Physical.hardware Toy16.sumProgram)', ['Designs.Toy16.Hardware', 'Designs.Toy16.Programs']),
        'circular': (f'(Fifo.Circular.Physical.hardware 4 {width})', ['Designs.Fifo.CircularHardware']),
        'ring': (f'(Fifo.Circular.Physical.hardware 4 {width})', ['Designs.Fifo.CircularHardware']),
    }[design]
    lean_format = FORMATS[format]
    out = ['import HDLean.Backend.Parse\n' + '\n'.join('import ' + m for m in modules),
           'open HDLean HDLean.Backend', f'namespace {namespace}',
           f'set_option maxRecDepth {1000000 if artifact.count(bytes([10])) > 8192 else 65536}\nset_option maxHeartbeats 16000000\nset_option linter.unusedSimpArgs false',
           f'def candidate : Graph := {graph_from_aiger(graph_aiger)}',
           '''private theorem normalize_cons (l next : List UInt8) (ls : List (List UInt8)) :
    Format.normalizeByteLines (l :: next :: ls) =
      Format.normalizeByteLines [l] ++ Format.normalizeByteLines (next :: ls) := by
  unfold Format.normalizeByteLines
  rw [List.map_cons, ← List.singleton_append, List.filter_append]
  rfl''']
    lines = artifact[:-1].split(b'\n')
    out.extend(encode_chunks(lines) if len(lines) > 8192 else encode_lines(lines))
    out.extend([
        'def bytes : String := asciiText (rawLines.flatMap (fun l => l ++ [10])) lines_ascii',
        f'''theorem graph_correct : candidate.Equivalent {circuit} := by
  apply Graph.validateLocal_sound (hint := Local.pointerHint)
  decide +kernel''',
        f'''private theorem tokens_valid :
    (match Format.{lean_format}.parseTokens tokens with
     | .error _ => false
     | .ok parsed => parsed.logic == candidate.logic) = true := by
  decide +kernel''',
        f'''theorem text_correct : Format.{lean_format}.Correct bytes {circuit} := by
  apply Format.correct_of_validated _ _ _ _ graph_correct
  unfold Format.validates Format.parse bytes
  rw [Format.tokenize_ascii_lines rawLines lines_ascii lines_noNL, lines_normalized]
  exact tokens_valid''',
        f'end {namespace}',
        f'def main : IO Unit := do\n  (← IO.getStdout).write {namespace}.bytes.toUTF8'])
    source = ('\n\n'.join(out) + '\n').encode()
    manifest = {'schema': 1, 'artifact_sha256': sha(artifact), 'artifact_bytes': len(artifact),
                'candidate_aiger_sha256': sha(graph_aiger), 'source_sha256': sha(source),
                'design': design, 'width': width, 'format': format,
                'roots': [namespace + '.graph_correct', namespace + '.text_correct']}
    return source, manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--artifact', type=Path, required=True)
    p.add_argument('--graph-aiger', type=Path, required=True)
    p.add_argument('--design', choices=['counter', 'fifo', 'pipeline', 'ram', 'toy16', 'circular', 'ring'], required=True)
    p.add_argument('--width', type=int, default=8)
    p.add_argument('--format', choices=FORMATS, required=True)
    p.add_argument('--namespace', required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    source, manifest = generate(args.artifact.read_bytes(), args.graph_aiger.read_bytes(),
                                args.design, args.width, args.format, args.namespace)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(source)
    args.output.with_suffix('.manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    main()
