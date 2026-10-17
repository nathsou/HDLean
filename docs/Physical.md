# Reproducible physical measurements

The FPGA flow emits the bit-blasted netlist of the word-level design the
correctness theorems are about (through the proved bit-blaster and emitter),
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

## Results

Reports are not committed: they go stale with every design, tool or constraint
change. Run the commands above, or the `Routed FPGA measurements` workflow, and read
the JSON reports it uploads. For scale, an earlier bit-level Toy16 (flip-flop memories)
routed at 47 MHz on an ECP5-25K and did not fit an iCE40HX8K.

Fmax is a tool/model estimate for register timing after placement and routing.
There are no external I/O delay constraints, board measurements, power estimates
or ASIC area claims. Changing device, tool release, ROM contents, constraints or
seed requires a new measurement. `synthesize.py` separately supports real
Liberty-based ASIC mapping when a process library is supplied.
