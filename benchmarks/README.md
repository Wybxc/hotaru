# Kernel benchmark protocol

This suite compares theorem construction through the public APIs of Hotaru,
HOL Light, and HOL4 on the same deterministic HOL tasks. It measures the
Hotaru Rust-to-Lean path, native OCaml HOL Light, and Poly/ML HOL4. It does not
measure proof search, tactics, library loading, Lean proof checking during the
build, or the time needed to compile any of the three systems.

## Workloads

The benchmark varies one cost driver at a time and includes a small complete
proof trace. Let `p : bool`, `f : bool -> bool`, and `f^d(p)` mean `d` nested
applications of `f` to `p`. All setup mentioned below happens before the
clock starts.

| Case | Timed transaction | Setup and expected theorem |
| --- | --- | --- |
| `refl_reuse/d` | `REFL` on one prebuilt `f^d(p)` | `|- f^d(p) = f^d(p)`, no assumptions |
| `refl_checked/d` | `REFL` on one prebuilt and prevalidated `f^d(p)` | The same theorem; Hotaru's checked term is held for the trial |
| `refl_retain/d` | The same `REFL`, retaining every result until the clock stops | The same theorem and prebuilt input |
| `refl_build/d` | Build a fresh `f^d(p)`, then call `REFL` | The same theorem; `f` and `p` are prebuilt |
| `assume/0` | `ASSUME p` | `p |- p` |
| `eq_mp/0` | `EQ_MP` on prebuilt `REFL p` and `ASSUME p` | `p |- p` |
| `trans_hyps/k` | `TRANS` on two prebuilt equality chains | `2k` distinct assumptions and conclusion `x0 = x(2k)` |
| `trace/0` | `REFL f`, `REFL p`, `MK_COMB`, `TRANS`, `ASSUME (f p)`, `EQ_MP` | `f p |- f p`; six rule calls per transaction |

The two equality chains in `trans_hyps/k` each carry `k` assumptions of the
form `x_i = x_(i+1)`. Their construction is excluded from the timed
transaction, so this case isolates the cost of combining existing theorem
assumptions. For `k = 0`, both premises are reflexivity theorems and the result
has no assumptions.

The live-result policy is part of the workload. Most cases keep at most 256
new results at a time and release each batch inside the timed interval.
`refl_retain` instead keeps all results until after the clock stops. Both
policies keep and validate the final theorem, and every trial checks its
conclusion and assumption count outside the timed interval.

The standard profile holds the iteration count fixed within each depth or
assumption-count sweep. It also uses the same count for `refl_reuse/0` and
`refl_retain/0`, so their difference isolates the live-result policy more
closely. Counts differ between workload families to keep each trial practical.

## Running

The runner builds the Hotaru release example and compiles the HOL Light source
with the installed `hol_light` OCaml package. HOL4 must already have a built
`bin/hol` heap, and its path is supplied explicitly. Python 3, Rust, Lean,
OCaml with `ocamlfind` and `camlp5`, and Poly/ML must be available for a
three-system run.

From the repository root, run a correctness smoke test first:

```sh
python3 benchmarks/run.py --profile smoke --systems all \
  --hol-light-switch /path/to/opam/switch \
  --hol4-bin /path/to/HOL/bin/hol
```

The standard profile uses the iteration counts in `STANDARD_CASES` in
[`run.py`](run.py), 2,048 warmup transactions per case, and seven timed trials
per case. Omit `--hol-light-switch` when the active environment already
provides `hol_light`; use `--systems hotaru` to run only Hotaru. A comparative
run is:

```sh
python3 benchmarks/run.py --profile standard --systems all \
  --hol-light-switch /path/to/opam/switch \
  --hol4-bin /path/to/HOL/bin/hol --trials 7
```

The smoke profile validates compilation, theorem results, and the output
protocol with only 256 transactions per case. Its timings are too short for
performance conclusions. The runner rejects missing, duplicate, malformed,
or mismatched case results even when an external prover exits successfully.

## Measurement and interpretation

Each timed trial reports elapsed nanoseconds for its full transaction count.
The clock includes theorem allocation, runtime memory management, and release
of batches in the bounded-live cases. It excludes initial theory creation,
input and premise setup, warmup, theorem validation, compiler work, process
startup, and output formatting. HOL Light and HOL4 perform a full garbage
collection before each timed trial; Hotaru uses Lean's normal runtime memory
management. Cases execute sequentially in one process per implementation.

The result is a JSON file under `target/benchmarks/` unless `--output` selects
another location. It contains every trial, a median and range in nanoseconds
per transaction, machine and toolchain metadata, and hashes of benchmark
sources and compiled artifacts. Raw trials are retained without outlier
removal. A single combined score is deliberately absent because the cases
measure different operations and live-set policies.

Comparative results require repeated standard runs on an otherwise idle,
fixed machine. Alternate the order in `--systems` across runs, keep compiler
and prover versions fixed, and compare distributions rather than one fastest
trial. The installed HOL Light package version and library hash identify the
actual linked artifact; a nearby HOL Light source checkout need not match it.

The timing boundary must accompany every published number. `refl_reuse`
excludes term construction but includes Hotaru's raw-term validation, while
`refl_build` includes both. `refl_checked` excludes Hotaru's one-time
`check_term` call and retains its typed term across the trial; the ML systems
use the same prebuilt term as `refl_reuse` because their constructors already
validate it. The six-step `trace` is a common logical task, but the
implementations may use different internal representations and derived-rule
paths. These results characterize the selected APIs, not the total capability
of each proof assistant.

Memory footprint, cold-start latency, theory loading, and tactic performance
are separate dimensions. The present runner does not report those metrics;
they should be measured and labeled separately instead of being folded into
kernel throughput.

## Extending the suite

A new standard case must define its logical inputs, expected conclusion and
assumptions, timed operations, result lifetime, parameter sweep, and fixed
iteration count within that sweep. It must have matching implementations in
all three programs and pass the smoke profile before its timing is compared.
The runner's case specification and strict result parser make omissions
visible. Workloads involving proof search belong in a separate suite with
their own success and timeout criteria.
