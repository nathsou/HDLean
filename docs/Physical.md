# Reproducible physical measurements

The FPGA flow emits the same physical AST used by the correctness theorems,
synthesizes it with Yosys/ABC, then places and routes it with nextpnr. A report is
written only after routing succeeds, resources fit, and timing meets the target.
Reports include artifact, executable and device-model hashes, tool versions,
package, seed, utilization and clock constraints. Failed routing produces logs
without a success report.

The pinned Linux x86_64 tool distribution is OSS CAD Suite **2026-10-14**,
SHA-256 `a6ccc6b96b2d985336a1061c78b2fd2bdd73e0f68690da17db88e00457881a11`.
It includes Yosys **0.70+16 / 3bb533450** and nextpnr
**0.11.1-63 / g44a6c739**. The bootstrap checks this hash before extraction and
redirects GUI wrapper cache/configuration writes into the explicit work directory.
It does not modify implementation binaries or device models.

```sh
lake build
python3 scripts/bootstrap_eda.py --output work/eda
export YOSYS="$PWD/work/eda/oss-cad-suite/bin/yosys"
export ABC="$PWD/work/eda/oss-cad-suite/bin/yosys-abc"
export NEXTPNR="$PWD/work/eda/oss-cad-suite/bin/nextpnr-ecp5"
python3 scripts/place_route.py counter --device ecp5-25k
python3 scripts/place_route.py pipeline --device ecp5-25k
python3 scripts/place_route.py toy16 --device ecp5-25k
```

The `Routed FPGA measurements` GitHub workflow runs these commands on demand and
uploads emitted RTL, mapped/routed artifacts, logs and reports. The archive is
approximately 748 MB compressed and 2.5 GB extracted.

## Recorded results

All three runs used **ECP5-25K, CABGA381, speed grade 6, seed 1, 12 MHz**. Pins were
assigned automatically. The complete CPU includes 256 sixteen-bit data words
implemented as flip-flops, eight registers, the immutable sum-program ROM and its
full 79-bit retirement interface.

| Design | Mapped combinational cells | Mapped flip-flops | Routed Fmax |
| --- | ---: | ---: | ---: |
| Decade counter | 12 / 24,288 | 4 / 24,288 | 361.01 MHz |
| Three-stage elastic FIFO pipeline, width 8 | 136 / 24,288 | 54 / 24,288 | 246.24 MHz |
| Complete Toy16 fetch/execute CPU | 12,629 / 24,288 | 4,234 / 24,288 | 47.02 MHz |

The machine-readable results are [counter](reports/counter-ecp5-25k.json),
[pipeline](reports/pipeline-ecp5-25k.json) and [CPU](reports/toy16-ecp5-25k.json).
The physical CPU AST has 4,288 bits; synthesis removes unused/padding bits, which
explains the lower mapped count. Its proved retirement bound remains two cycles.

An earlier Yosys 0.52 run on the same ECP5 target achieved 45.63 MHz with 12,750
combinational cells. The current table uses the fully pinned distribution above.
The full CPU exceeded iCE40HX8K capacity (8,918 / 7,680 logic cells); that failure
is not a successful device result. `place_route.py` also supports smaller iCE40
designs with the installed chip database specified by `--chipdb-model`.

Fmax is a tool/model estimate for register timing after placement and routing.
There are no external I/O delay constraints, board measurements, power estimates
or ASIC area claims. Changing device, tool release, ROM contents, constraints or
seed requires a new measurement. `synthesize.py` separately supports real
Liberty-based ASIC mapping when a process library is supplied.
