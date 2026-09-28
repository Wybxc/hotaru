# LIST_NOT_NIL results (2026-09-29)

The fixed-certificate comparison measures complete import of the same
88,221-line HOL4 proof in all three systems. Historical rows combine standard
runs with reversed system order, while the Sep 29 rows record
source-synchronized seven-trial runs. The article, external theorem inputs,
validation, and timing boundary are described in the [protocol](README.md).

| Adapter and run date | Hotaru | HOL Light | HOL4 |
| --- | ---: | ---: | ---: |
| Eager equality conversion, Sep 27 | 126.094 ms (119.443-136.569) | 13.643 ms (13.134-14.154) | 65.603 ms (62.010-79.366) |
| On-demand equality conversion, Sep 28 | 68.362 ms (64.641-81.715) | 14.787 ms (13.555-17.609) | 66.779 ms (62.919-76.955) |
| On-demand conversion with transparent public API, Sep 28 | 50.415 ms (45.833-62.300) | 13.080 ms (12.281-13.917) | 63.085 ms (57.936-82.894) |
| Kernel-resident bidirectional HOL equality normalization with HOL4-style `inst_ty_term`, current public API, Sep 28 | 17.274 ms (16.886-18.613) | 12.869 ms (12.361-13.407) | 61.936 ms (58.488-68.411) |
| Representation-transparent FFI with one opaque theorem form, Sep 29 | 16.680 ms (16.386-17.588) | 12.992 ms (12.633-13.268) | 62.734 ms (58.972-67.998) |
| Semantic FFI with reused certificate state and one-pass decoding, Sep 29 | 15.629 ms (15.459-15.930) | 12.953 ms (12.546-14.107) | 63.690 ms (61.617-69.790) |
| Semantic FFI with verified single-pass type/term instantiation, Sep 29 | 15.446 ms (15.324-15.589) | 12.861 ms (12.452-13.019) | 62.967 ms (59.417-67.767) |

On-demand conversion reduces Hotaru's median import time by about 46% while
leaving the checked article and kernel rules unchanged. A same-day rerun of
the preserved eager binary measured 126.393 ms (125.306-127.008) over seven
trials, confirming an approximately 1.85x speedup under the new run's machine
conditions. The current representation-transparent adapter measures 16.680 ms
per import in the source-synchronized run, while HOL Light measures 12.992 ms
and HOL4 measures 62.734 ms. The current semantic-interface adapter measures
15.446 ms, while HOL Light measures 12.861 ms and HOL4 measures 62.967 ms.
This is about 1.20 times slower than HOL Light and about 4.1 times faster than
HOL4 on this workload; it does not establish a lead over both systems.

The current adapter crosses zero representation boundaries because equality
alignment is part of the ordinary kernel rules. Its single-import trace has 9
explicit `contract` calls, and every certificate rule and final theorem check
remains in the timed and validated path.

`EQ_MP` and `DEDUCT_ANTISYM` return semantically equivalent assumption lists
with duplicates removed inside their verified rules, so the adapter does not
expose a housekeeping fusion rule or issue a second contraction for those
results. Their verified implementations pass through the nonempty list when
the other input is empty and allocate a deduplicated union only when both
inputs are nonempty; the adapter uses the same fact to avoid an FFI count
lookup in the empty-context cases. The combined type/term instantiation path
is exposed as the HOL4-style `inst_ty_term` rule.

The current `inst_ty_term` implementation performs type instantiation and free
variable substitution in one verified term traversal. Its Lean theorem proves
equality with the former two-rule composition, so the FFI contract and checked
theorem are unchanged; the 15.446 ms run is lower than the preceding 15.629 ms
run, while the overlapping ranges do not establish a stable improvement by
themselves.

The adapter keeps one theorem object per proof instead of maintaining separate
article and native equality caches. This removes redundant conversion and
metadata work while leaving the same rule inputs, kernel checks, and final
theorem validation in place.

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
Certificate reading, term construction, Rust-to-Lean calls, kernel-side
equality alignment, and explicit assumption compaction remain inside Hotaru's
timed interval. The separate [public API results](../RESULTS.md) compare
common kernel-rule workloads and show where Hotaru is faster or slower through
that interface.

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
(results/replay-public-ordinary-reverse-20260928.json). The current
representation-transparent run is [standard]
(results/replay-transparent-standard-20260929.json). The current optimized
semantic-interface run is [standard]
(results/replay-semantic-ffi-optimized-standard-20260929.json). The verified
single-pass kernel run is [standard]
(results/replay-single-pass-kernel-standard-20260929.json).
