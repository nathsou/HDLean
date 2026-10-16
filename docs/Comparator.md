# Isolated comparison against an approved reference

`scripts/comparator/compare.py` compares a submitted Lean block with an independently approved reference, replays its proof closure, and binds its approved artifact theorem to the exact emitted bytes. `scripts/verify.py` continues to produce an L1 development report. It does not grant reference approval or silently upgrade that report.

The comparator must be installed and invoked from a trusted location outside the submitted tree. A reviewer supplies both a receipt and its SHA-256 digest through a separate trusted channel. A candidate-provided receipt, a digest computed from that receipt by the candidate, or this repository's development manifest is not independent approval. The fixture receipts in the test suite approve only synthetic test blocks; they do not approve HDLean's specification.

## Invocation

```sh
python3 /trusted/hdlean/scripts/comparator/compare.py \
  --reference /trusted/reviewed-reference \
  --candidate /submissions/candidate \
  --receipt /trusted/approval.json \
  --approval-sha256 REVIEWER_SUPPLIED_SHA256 \
  --toolchain /trusted/lean-4.34.0-linux \
  --tools /trusted/independent-tools/tools.json \
  --output /trusted/results/submission-001 \
  --level L3
```

Use `scripts/independent/bootstrap.py` to pin the exporter and nanoda bundled with the Lean 4.35.0 toolchain. Lean 4.35.0 also ships `lake comparator`, which covers statement comparison, axiom policy, sandboxing and multi-kernel replay; this comparator remains for the two checks it adds, exact byte binding and authentication of the primitive foundation. The receipt pins the exact binaries as well as the toolchain version, the complete Lean toolchain tree, and the bubblewrap executable. The OS kernel, Python interpreter, comparator installation and host runtime libraries are trusted deployment dependencies. Deploy them from a reviewed, immutable installation. The sandbox mounts `/usr`, `/bin`, `/lib` and `/lib64` read-only for those runtime libraries and programs; it does not mount the host home, `/etc`, or workspace. Use a dedicated runner whose mounted runtime trees contain no confidential data. OS and runtime image identity must be established by the trusted deployment; the receipt does not hash those whole system trees.

A missing or unusable Linux namespace sandbox is a hard failure. This workspace blocks bubblewrap's network namespace setup (`NETLINK_ROUTE`); no local isolated acceptance is claimed. CI sets `HDLEAN_REQUIRE_SANDBOX=1`, so unavailable isolation fails the test job instead of skipping it. Ordinary local unit tests may skip only the namespace integration class and report that skip explicitly.

## Receipt schema

The receipt has exactly these fields (schema version 1):

| Field | Meaning |
| --- | --- |
| `schema` | `1` |
| `reference_sha256` | `canonical.digest(snapshot(reference))` from the trusted comparator |
| `toolchain_sha256` | `canonical.digest(snapshot(toolchain, filtered=False))` |
| `tools_pins` | Exact `pins` object from the independent tool manifest |
| `tool_binaries` | `exporter` and `checker` SHA-256 values |
| `sandbox_sha256` | SHA-256 of the approved bubblewrap executable |
| `modules` | Modules to import and freshly check |
| `build_targets` | Explicit Lake build targets |
| `roots` | Required theorem names with approved statements |
| `protected_declarations` | Additional declarations whose full bodies and types are frozen |
| `implementation_declarations` | Explicit, reviewer-approved safe definitions whose bodies may change; may be empty |
| `protected_files` | Relative source path to SHA-256 map, mounted read-only during builds |
| `artifacts` | Artifact specifications described below |
| `limits` | All resource-limit keys described below |

Each artifact specification contains exactly `path`, `module`, `bytes`, `correctness_root`, and `generate`. `path` is a relative path to the generated file; `module` supplies its Lean declarations; `bytes` names a `String` definition; `correctness_root` must be an approved theorem whose actual type mentions that definition. `generate` is an argument array executed inside the sandbox, such as `["/work/.lake/build/bin/artifact"]`. Review must establish that this theorem states the intended semantics, not a trivial property. The tool then enforces that precise approved statement.

`implementation_declarations` permits implementation changes without allowing specification changes. Every hole must remain a safe definition of exactly the same actual type. The comparator protects the entire transitive definition closure reachable from theorem types, following bodies of predicates such as `Safe` and their helper definitions. At an approved implementation hole it follows the type but stops before the implementation body. Names cannot be added to this exception list by the submission. Holes may not overlap the mandatory primitive foundation or any of its transitive dependencies. Protect source files containing specification, transition model and safety predicates; body comparison also detects a fabricated `.olean` with a weakened definition despite unchanged source files.

Receipt generation and digest calculation are mechanical preparation steps. They do not constitute reviewer approval. The reviewer must approve the reference, statements, implementation holes, artifact semantics, generation commands, protected inputs and resource bounds before supplying the final digest.

## Checks and boundaries

1. Validate the externally supplied digest, receipt schema, tool pins, reference snapshot, protected sources and source-size bounds. Reject symlinks, path traversal and prebuilt source artifacts. Approved internal toolchain file links are hashed together with their targets and cannot leave the toolchain tree.
2. Copy fresh sources without `.lake`, `build`, `work` or `.git`. Build reference and candidate in separate bubblewrap processes with new user, process, mount and network namespaces, no capabilities, disabled nested user namespaces, an empty environment and read-only protected source mounts. Candidate native build code executes only in this isolation.
3. Generate the listed artifacts, verify that source inputs did not change, and run `leanchecker --fresh` on the approved modules with the stage mounted read-only.
4. Generate and kernel-check a theorem equating each candidate byte definition to the literal contents of its actual artifact. Printable ASCII plus tab, CR and LF are supported, with a 64 MiB aggregate literal-binding limit across unique artifact paths. Reject symlinks at every artifact path component. This binding uses kernel reduction, including when native code overrides the compiled value of a logical definition.
5. Export the roots, approved declarations and byte-binding theorems. Replay the untouched export with nanoda, allowing only `propext`, `Classical.choice` and `Quot.sound`. All three axiom declarations are always explicitly exported and their actual types/bodies compared with the trusted reference, regardless of whether the theorem-type closure uses them; a permitted name cannot conceal a forged axiom such as `propext : False`. The finite primitive name cache of the pinned checker is also exported from `Init` and authenticated, including natural-number operations, string/list/character constructors, quotient primitives and `eagerReduce`. The full transitive declaration closure of this foundation is protected without implementation holes. This is necessary because native extension reductions dispatch by constant name: a well-typed forged `Nat.add` body can otherwise disagree with native addition while passing nanoda. Both requested L2 and L3 modes require this independent authentication: potentially hostile native initializers must not be able to establish acceptance by forging exporter output or a fresh-checker success alone. Consequently L2 currently accepts only the same stricter, no-native-axiom subset.
6. Compare canonical actual theorem types and protected declaration bodies. Fingerprints retain constant identities, universes, de Bruijn indices, bodies, constructor order and recursor rules; they ignore exporter allocation IDs, binder spelling and irrelevant definition-height hints. Independently inspect each byte-binding theorem's actual type to require precisely `Eq String approvedBytes actualLiteral`.
7. Recheck the reference, submission, receipt and trusted tool hashes. Write `acceptance.json` only after all checks succeed. Remove a stale acceptance report before each attempt.

Resource limits are required positive integers: `memory_mb` (aggregate descendant resident-memory watchdog), `address_mb` (per-process OS virtual-address-space limit), `cpu_seconds` (per-process CPU limit), `wall_seconds` (per-command wall deadline), `file_mb` (per-file size limit), `temp_mb` (sandbox tmpfs size), `work_mb` (aggregate writable-tree watchdog), `source_mb` and `source_files`. Process count and open files are also bounded. The resident-memory and writable-tree watchdogs poll and can overshoot between polls; they are not cgroup limits or filesystem quotas. The default 64 GiB virtual-address limit accommodates Lean's sparse allocator reservations while the separate 6 GiB resident budget constrains actual memory use. Sandbox Lean runtime threads are limited to two; approved Lake configurations should also supply `moreLeanArgs = ["-j2"]` because Lean's command-line frontend separately chooses its thread count. Limits apply separately to each build/check command, not as a single aggregate job budget. Proof canonicalization runs in its own resource-bounded trusted subprocess. A deployment should also apply whole-job cgroup and disk quotas to its dedicated worker.

The acceptance report covers exactly the receipt's blocks and artifact files. The compiler and runtime are not promoted into proof authorities; valid kernel/nanoda proofs and the literal byte binding are required. The large Toy16 exact-byte certificate remains beyond the measured kernel resource budget, so its native emission, generic correctness theorems, and external equivalence results do not imply a successful exact-byte L3 acceptance.

## Tests

```sh
# Genuine isolation is mandatory on the CI runner.
HDLEAN_REQUIRE_SANDBOX=1 python3 -m unittest discover \
  -s Tests/comparator -p 'test_*.py' -v
```

The suite accepts a different correct implementation (`n + 0` to `0 + n`) and different valid artifact bytes under approved holes. It rejects a valid proof of the wrong statement, a hidden axiom, a changed protected source, a native `implemented_by` byte override, and a valid replacement `.olean` containing a weakened specification. Native candidate code also attempts a protected-source write and an outbound connection; both must fail. Accepted and rejected runs retain logs under `build/comparator-tests/` for CI review. Additional local tests cover approval mismatch, actual type/body comparison, symlink redirection, source bounds, mandatory namespace flags and resource timeout.

A regression fixture exports `Probe.arithmetic : Nat.add 0 0 = 0` and a replacement addition body returning 1. The test confirms that pinned nanoda accepts the altered export, then requires reference foundation comparison to reject it. It also rejects an attempted implementation hole in the foundation. The fixture was produced with the toolchain's `leanexport` (Lean 4.35.0) from `Tests/comparator/fixtures/NativeExtension.lean`; the immutable NDJSON fixture keeps this security test independent of candidate build code.
