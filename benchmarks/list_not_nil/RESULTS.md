# LIST_NOT_NIL results (2026-09-28)

The fixed-certificate comparison measures complete import of the same
88,221-line HOL4 proof in all three systems. Each standard run has seven
trials of 16 imports, and each reported median combines two runs with the
system order reversed. The article, external theorem inputs, validation, and
timing boundary are described in the [protocol](README.md).

| Adapter and run date | Hotaru | HOL Light | HOL4 |
| --- | ---: | ---: | ---: |
| Eager equality conversion, Sep 27 | 126.094 ms (119.443-136.569) | 13.643 ms (13.134-14.154) | 65.603 ms (62.010-79.366) |
| On-demand equality conversion, Sep 28 | 68.362 ms (64.641-81.715) | 14.787 ms (13.555-17.609) | 66.779 ms (62.919-76.955) |
| On-demand conversion with transparent public API, Sep 28 | 50.415 ms (45.833-62.300) | 13.080 ms (12.281-13.917) | 63.085 ms (57.936-82.894) |
| Cached ordinary-rule bridge with HOL4-style `inst_ty_term` and semantic context contraction, current public API, Sep 28 | 27.600 ms (24.729-30.348) | 13.169 ms (12.695-13.807) | 64.036 ms (58.520-68.639) |

On-demand conversion reduces Hotaru's median import time by about 46% while
leaving the checked article and kernel rules unchanged. A same-day rerun of
the preserved eager binary measured 126.393 ms (125.306-127.008) over seven
trials, confirming an approximately 1.85x speedup under the new run's machine
conditions. The current cached ordinary-rule bridge and semantic context
normalization measure 27.600 ms per import in the combined run, while HOL
Light measures 13.169 ms and HOL4 measures 64.036 ms. The original 9.2x gap
to HOL Light was therefore substantially caused by eager conversions in
Hotaru's importer.

The current adapter converts an equality proof only when a later rule needs its
other representation, while keeping that representation private to the
certificate reader. It constructs the bridge from the existing checked kernel
rules, so the public FFI exposes only native equality operations. The current
single-import trace records 878 representation-boundary conversions and 9
explicit `contract` calls, and each conversion still constructs a
kernel-checked proof; no certificate rule or theorem check is skipped.

`EQ_MP` and `DEDUCT_ANTISYM` return semantically equivalent assumption lists
with duplicates removed inside their verified rules, so the adapter does not
expose a housekeeping fusion rule or issue a second contraction for those
results. Their verified implementations pass through the nonempty list when
the other input is empty and allocate a deduplicated union only when both
inputs are nonempty; the adapter uses the same fact to avoid an FFI count
lookup in the empty-context cases. The combined type/term instantiation path
is exposed as the HOL4-style `inst_ty_term` rule.

The adapter also records the representation produced by each certificate rule
instead of inspecting every returned theorem conclusion through the FFI. This
removes redundant metadata calls while leaving the same rule inputs, kernel
checks, and final theorem validation in place.

The three provers validate the same mathematical conclusion but retain
different proof representations. Hotaru checks the OpenTheory article and
compares its final lambda-encoded equality term with the expected proposition;
HOL Light matches the conclusion with `term_match` and `aconv`; and HOL4
compares it with the library theorem `LIST_NOT_NIL` using `Term.aconv`. All
three checks require an empty final hypothesis list, while the 31 imported
theorem inputs are represented as theory axioms in Hotaru and as matched
library theorems in the other two systems. The internal derivation trees and
theorem objects are therefore not expected to be identical even though the
checked proposition is alpha-equivalent.

The earlier direct-conversion experiments used an encoding-specific Lean
export and are excluded from the current protocol because that entry point
leaks the certificate adapter's representation. Their raw files remain only as
historical implementation comparisons, not as supported interface
measurements.

The adapter also lowers this process's peak resident memory on the measured
workload. Two measurements per adapter, ordered eager/on-demand/on-demand/eager
and each containing one warmup and one timed trial of 16 imports, measured
116.7 MiB for eager conversion and 103.2 MiB for on-demand conversion. These
are whole-process peaks, including the Lean runtime and importer setup,
rather than isolated proof-cache sizes.

The remaining import-time difference does not isolate the Lean kernel.
Certificate reading, term construction, Rust-to-Lean calls, conversion proofs,
and explicit assumption compaction remain inside Hotaru's timed interval. The
current source-synchronized rerun is about 2.1 times slower than HOL Light and
about 2.3 times faster than HOL4 on this workload, so it does not establish a
lead over both systems. The separate [public API results](../RESULTS.md) compare common
kernel-rule workloads and show where Hotaru is faster or slower through that
interface.

The native-proof results measure a different task from certificate import.
HOL4 runs the source `metis_tac` proof and HOL Light performs a list case
split and rewrite; Hotaru has no corresponding tactic layer. Their earlier
standard medians were 2.351 ms (2.252-2.598) for HOL4 and 0.0766 ms
(0.0752-0.0790) for HOL Light, so they should not be compared with import
times.

The raw files preserve the trials and implementation hashes for each import
adapter: [eager forward](results/replay-forward-20260927.json),
[eager reverse](results/replay-reverse-20260927.json),
[on-demand forward](results/replay-lazy-forward-20260928.json), and
[on-demand reverse](results/replay-lazy-reverse-20260928.json). The historical
[optimized forward](results/replay-final-alias-forward-20260928.json) and
[optimized reverse](results/replay-final-alias-reverse-20260928.json) runs
are retained as adapter variants. The
[same-day eager control](results/replay-eager-control-20260928.json) records
the preserved binary's trials and rule counts, while the
[memory control](results/memory-control-20260928.json) records individual
peak-RSS runs. The [native forward](results/native-forward-20260927.json)
and [native reverse](results/native-reverse-20260927.json) files preserve the
separate tactic measurements. The current public-rule runs are [forward]
(results/replay-public-ordinary-forward-20260928.json) and [reverse]
(results/replay-public-ordinary-reverse-20260928.json).
