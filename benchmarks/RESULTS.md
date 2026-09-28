# Public API benchmark results (2026-09-28)

These measurements compare common theorem-construction transactions through
Hotaru's Rust API, HOL Light's OCaml API, and HOL4's Poly/ML API on one macOS
arm64 machine. The table reports the median of 14 per-transaction trials
from two standard runs in opposite system orders. The [protocol](README.md)
defines each transaction and its live-result policy.

| Transaction | Hotaru | HOL Light | HOL4 |
| --- | ---: | ---: | ---: |
| `refl_reuse/0` | 35.0 ns | 10.1 ns | 45.0 ns |
| `refl_reuse/256` | 8.89 us | 10.3 ns | 47.9 ns |
| `refl_checked/0` | 14.7 ns | 10.0 ns | 46.5 ns |
| `refl_checked/256` | 14.1 ns | 10.4 ns | 47.7 ns |
| `refl_retain/0` | 29.7 ns | 78.2 ns | 228.6 ns |
| `eq_mp/0` | 51.6 ns | 6.0 ns | 17.8 ns |
| `trans_hyps/0` | 70.4 ns | 7.5 ns | 71.9 ns |
| `trans_hyps/8` | 120.9 ns | 518.3 ns | 636.6 ns |
| `trans_hyps/64` | 469.0 ns | 4.71 us | 4.61 us |
| `trace/0` | 428.7 ns | 47.1 ns | 311.3 ns |

Repeated raw-term checking dominates Hotaru's `REFL` time at depth 256.
Its prechecked `REFL` stays near 14 ns across term depths, showing that the
8.89 us raw-term result chiefly measures validation at the API boundary.
The ML benchmarks use the same prebuilt term for `refl_reuse` and
`refl_checked`, so those cases are the same operation for them.

Small proof rules still cost more through Hotaru's public API. With prebuilt
premises, `EQ_MP` is about 2.9 times HOL4's time and 8.6 times HOL Light's;
the six-rule trace is about 1.4 and 9.1 times their respective times. These
measurements include Rust-to-Lean calls, allocations, and runtime memory
management, so they do not by themselves quantify time spent inside the
Lean kernel.

Assumption handling changes the ranking as the context grows. Hotaru's
`TRANS` appends assumption lists and takes 469 ns at 64 distinct assumptions
per premise, while both ML systems take about 4.6-4.7 us. Hotaru defers
duplicate removal until the `CONTRACT` structural rule; that extra work is included
in the [LIST_NOT_NIL import](list_not_nil/RESULTS.md), so the `TRANS` result
alone is not an end-to-end context-management comparison.

The results characterize distinct costs rather than one universal kernel
speed ratio. A Lean-side batched measurement would be needed to separate
Hotaru's internal rule execution from its public API and FFI cost. The
[forward raw trials](results/kernel-api-forward-20260928.json) and
[reverse raw trials](results/kernel-api-reverse-20260928.json) include all
18 workloads, source hashes, binary hashes, and environment metadata.
