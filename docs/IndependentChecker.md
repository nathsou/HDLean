# Independent proof replay

`scripts/independent/replay.py` exports explicitly requested theorem roots and their
complete dependency closure, then checks the unmodified export with nanoda, a Rust
implementation independent of Lean's kernel. The replay layer is suitable for the
kernel-only proof requirement of L3. It does not itself provide submission
isolation, reviewer approval, physical sign-off, or select the required challenges.
The enclosing comparator must enforce those requirements and provide its complete
required theorem list.

## Pinned compatibility

The exact revisions are recorded in `scripts/independent/pins.json`:

| Component | Version / revision |
| --- | --- |
| Lean | 4.34.0, matching `lean-toolchain` |
| Rust | 1.90.0 |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` (v4.34.0) |
| nanoda | `f67473ba5f9397266f89c7852082c9c914b5d219` (0.4.24) |
| Export format | NDJSON 3.1.0 |

Both upstream tools build without patches. Nanoda's older `debug` branch expects
the obsolete text export format and is incompatible with this pipeline. Do not
substitute that branch or a floating exporter release.

## Build and run

Prerequisites are Python 3.10+, Git, a C compiler/linker, the project's Lean
toolchain, and rustup. Install the pinned Rust compiler if necessary:

```sh
rustup toolchain install 1.90.0 --profile minimal
python3 scripts/independent/bootstrap.py --lake lake --cargo cargo
lake build
lake build Tests.Certificates
python3 scripts/independent/replay.py \
  --module HDLean --module Designs --module Tests.Certificates \
  --theorem HDLean.Backend.Graph.validate_sound \
  --theorem HDLean.Tests.fifo1_graph \
  --theorem HDLean.Tests.counter_graph \
  --theorem HDLean.Tests.fifo8_graph
python3 -m unittest discover -s Tests/independent -p 'test_*.py' -v
```

The example deliberately names four graph theorems; its success covers precisely
those roots and their dependencies. The comparator must pass all required roots
for its assurance claim. The API is
`replay(project, lake, tools_manifest, output, roots, modules, timeout=600)`.
No default subset is silently substituted. Build the selected modules before
calling it; the replay wrapper does not perform the comparator's clean build.

The bootstrap fetches immutable Git revisions, uses Cargo's committed lockfile,
limits Rust compilation to two jobs, and records executable SHA-256 digests in
`work/independent-tools/tools.json`. `--cache` changes that location. To install
Rust outside the home directory, set `CARGO_HOME` and `RUSTUP_HOME` to directories
under `work/`, use rustup's `--no-modify-path` installation option, and put the
resulting Cargo `bin` directory on `PATH`. The same environment must be present
when running the bootstrap. `LAKE`, `CARGO`, and the explicit `--lake`/`--cargo`
options support nonstandard tool locations; tests honor `LAKE` and
`HDLEAN_INDEPENDENT_TOOLS`.

## What is checked

The exporter receives a nonempty, explicit, unique root list. The wrapper verifies
that every requested root appears as a theorem, checks Lean/format versions,
rejects unsafe/partial declarations, and permits only `propext`,
`Classical.choice`, and `Quot.sound`. No export records are removed. Nanoda
independently enforces the same axiom policy with
`unpermitted_axiom_hard_error: true` and `unsafe_permit_all_axioms: false`, then
typechecks the entire exported closure. Native-evaluation axioms, `sorryAx`, and
foreign axioms fail even when they are exported but unused.

A successful replay requires both a zero exit status and nanoda's unqualified
`Checked ... declarations with no errors` response. Failures remove any previous
`replay.json` before starting, so stale success reports are not reused. The result
records roots, encountered axioms, checked declaration count, tool pins, binary
digests, tool-manifest digest, and the proof-export digest. The export, nanoda
configuration, and logs remain in `build/independent/` for review.

The tool manifest is a provenance record created in the trusted build environment,
not an authorization token supplied by a submission. The enclosing comparator
must protect the checker scripts, pins, tools, manifest, required root list, and
build outputs against submission writes. A malicious replacement of both the
binary and its manifest is outside this wrapper's standalone protection. Hashes
detect persistent changes during replay; process/filesystem isolation is needed
against adversarial concurrent modification. The wrapper checks proof validity,
while statement/challenge identity remains the comparator's responsibility.

## Rejection tests

`Tests/independent/Fixtures.lean` is intentionally excluded from the project's
normal Lean library. The Python test copies it into an isolated temporary Lake
project. It includes a valid theorem and negative fixtures using a foreign axiom,
`sorry`, and `native_decide`. Tests require both the wrapper and the actual nanoda
binary to reject the three axiom cases. A separate mutation changes a valid
theorem's exported proof term to an ill-typed expression; the policy audit accepts
the artifact's coverage while nanoda rejects its proof. Additional tests cover
missing/duplicate/empty roots, stale success removal, and modified binary hashes.
Tests skip with an explicit message if the pinned tools have not been built;
release verification must require the tools and run these tests without skips.

## Exact backend bytes

`python3 scripts/verify.py --certify-bytes` adds independently replayed proofs for
Counter and FIFO8 in AIGER, SystemVerilog, and RTLIL; it also enables the headline
independent replay. CI runs this option. Each artifact gets a separate kernel
process with a default 6144 MB limit, controlled by `--certificate-memory-mb`.
The largest current fixture, FIFO8 RTLIL (50,337 bytes), took 59 seconds and
approximately 5.2 GB peak resident memory on the development host. Certificates
run sequentially. These are logical correctness checks, not physical sign-off.

A single artifact can be certified with:

```sh
python3 scripts/independent/certify_artifact.py \
  --artifact build/backend-checks/counter_8.sv \
  --graph-aiger build/backend-checks/counter_8.aiger \
  --design counter --format sv --output build/certify-counter-sv
```

`byte_certificate.py` reads the actual artifact as bytes and an AIGER graph
candidate. It emits an explicit graph, raw ASCII line definitions, local proofs
of line validity and normalization, and the final `graph_correct` and
`text_correct` theorems. Repeated lines share definitions. The generic proved
`Format.tokenize_ascii_lines` lemma connects the exact `asciiText` byte array to
those normalized lines. Parsing the complete token stream and graph validation
are checked with `decide +kernel`; no native evaluation axiom is introduced.
The final theorem is `Format.Correct bytes <the selected circuit>`, covering
all pre-edge states, inputs, and reset values of that circuit instance.

`certify_artifact.py` builds a content-addressed module, executes its compiled
byte definition, compares every byte with the input artifact, independently
replays both theorem roots, and checks that artifacts and generated source did
not change. `certificate.json` records the exact artifact and graph hashes,
generated-source hash, selected design/width/format, explicit theorem roots,
resource bound, and nested nanoda report. A failure deletes stale success first.
The enclosing verification report checks those bindings again. The generator,
wrapper, source modules, and binaries remain part of the protected comparator
surface; hostile concurrent filesystem mutation requires process isolation.

The byte integration tests also reject an inverted clock and a valid proof for
a semantically equivalent file with different raw bytes. Thus semantic validity
alone cannot silently substitute a different artifact.

## Local graph certificates and large instances

`Graph.validateLocal_sound` validates ordered gate equations and proof-carrying
source-expression memo entries. AND lookups use ordered finite maps, and cache
reuse checks structural equality before accepting a saved meaning. The arbitrary
hint function is not an assumption: constant, colliding and pointer hints cannot
turn a wrong graph into a valid proof. Native construction uses pointer hints;
logical/kernel reduction uses the transparent structural fingerprint. Tests cover
constant/adversarial hints, wrong roots, altered gates and the complete Toy16 AST.

The exact-byte generator supports counter, FIFO, elastic pipeline, RAM, circular
FIFO and Toy16 constructors. Files over 8,192 lines use compositional 64-line
lexical chunks and bounded graph-array literals. Support in a generator does not
mean every generated certificate fits available checker resources. The six
counter/FIFO8 format certificates passed kernel and nanoda replay; the full CPU
AIGER attempt exceeded a 6 GiB allocation cap during lexical checking and emitted
no success report. A separate CPU graph-only kernel attempt reached over 7 GiB
process memory. Native local validation, generic soundness and replayed hardware
proofs are not labeled as a successful concrete CPU byte certificate.

All 77 current headline roots have independently replayed in nanoda over 6,680
declarations. That closure includes general circular FIFO and physical async FIFO
proofs, finite latency/retiming, reset reassertion, invariant-certificate soundness,
physical CPU retirement/progress and generic parsed-text semantics. It is separate
from the exact-byte artifact closures above.
