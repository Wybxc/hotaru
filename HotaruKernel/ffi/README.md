# C interface (ABI 1)

The C interface executes the Lean kernel through an opaque immutable state.
It supports macOS and Linux and requires the pinned Lean 4.29.0 installation
and a system C compiler with POSIX threads. It owns Lean initialization and
must not share a process with another independently initialized Lean host.

## Build and test

From `HotaruKernel/`:

```sh
lake build hotaruC
lake build hotaruCTest
.lake/build/bin/test_hotaru
```

The library is `.lake/build/lib/libhotaru.dylib` on macOS or
`.lake/build/lib/libhotaru.so` on Linux. The public header is `ffi/hotaru.h`.
The build embeds a search path to this toolchain's shared libraries. Distributing
the library requires distributing the matching runtime libraries and adjusting
loader paths; the output is not a standalone runtime-free binary.
The first native build also compiles the export module's transitive imports.
On macOS, Lake's default linker environment uses a future deployment-version
marker. Set `MACOSX_DEPLOYMENT_TARGET` when building for a particular macOS
deployment target; the generated objects and matching Lean runtime must also
support that target.

`lake build` still builds only the kernel. `lake test` includes the Lean JSON
behavior checks. CI explicitly builds and runs the C integration tests as well.
The custom native targets live in `lakefile.lean`; dependency revisions and
the existing `lake-manifest.json` lock are unchanged.

## Example

```c
#include "hotaru.h"
#include <stdio.h>
#include <string.h>

int main(void) {
    hotaru_state *base = NULL, *next = NULL;
    char *response = NULL;
    if (hotaru_state_new(&base) != HOTARU_OK) return 1;
    const char *commands =
        "[{\"infer\":{\"rule\":{\"refl\":{\"p\":{\"fvar\":[\"p\",\"bool\"]}}}}}]";
    int status = hotaru_apply(base, commands, strlen(commands), &next, &response);
    if (response) puts(response);
    hotaru_string_free(response);
    if (status == HOTARU_OK) {
        status = hotaru_theorem(next, 4, &response);
        if (response) puts(response);
        hotaru_string_free(response);
    }
    hotaru_state_free(next);
    hotaru_state_free(base);
    return status == HOTARU_OK ? 0 : 1;
}
```

For a source file `example.c`, compile and run from this directory's parent:

```sh
cc example.c -Iffi -L.lake/build/lib -lhotaru \
  -Wl,-rpath,"$PWD/.lake/build/lib" -o example
./example
```

## Ownership and errors

All state operations must run on the OS thread that first initializes the
library. Other threads receive `HOTARU_WRONG_THREAD`. Rust wrappers should make
state handles neither `Send` nor `Sync`, or put all calls on a dedicated worker.
The runtime stays initialized until process exit.

Inputs are borrowed for the duration of each call. Outputs are owned: release
states with `hotaru_state_free` and JSON strings with `hotaru_string_free`.
All handles must be live pointers returned by this library. Do not fabricate,
double-free, use freed handles, or overwrite an owned handle without releasing
it. Output slots must not alias each other or input memory. NULL frees succeed.

`hotaru_apply` executes a JSON array of commands atomically. Success returns a
new state and `{"ok":true,"theoremCount":N}`. The input state remains usable.
Rejection returns no state and `{"ok":false,"kind":K,"error":E}`; `kind` is
`json`, `command`, or `kernel`. Kernel errors are constructor names such as
`"freeInAssumptions"`. Earlier commands in a rejected batch are not published.
Invalid C arguments and invalid UTF-8 return `HOTARU_INVALID_ARGUMENT` without
a JSON response. Other C failures likewise leave outputs NULL.
`HOTARU_OUT_OF_MEMORY` covers adapter allocations; Lean runtime allocation
failure or a panic can terminate the process and is not a recoverable C error.

The initial state's theorem indices are 0: eta, 1: selection, 2: infinity,
3: Boolean cases. New theorems append; declarations add no theorems.
Indices are local to the state supplied to the call. There is no cross-state
theorem import API. `hotaru_theorem` returns structured assumptions and conclusion,
or a rejection for an out-of-range index.

## JSON protocol

ABI 1 uses the derived Lean JSON encoding below. The ABI version must change
if the wire format changes. Qualified names have `theory` and `name` fields.
Type substitutions are arrays of `[variableName, type]` pairs.

| Type | JSON |
| --- | --- |
| Boolean | `"bool"` |
| Type variable | `{"var":"a"}` |
| Function | `{"fn":[domain,range]}` |
| Type operator | `{"op":[qualifiedName,[arguments]]}` |

| Term | JSON |
| --- | --- |
| Free variable | `{"fvar":[name,type]}` |
| Bound variable | `{"bvar":index}` |
| Constant instance | `{"const":[qualifiedName,substitution]}` |
| Application | `{"app":[function,argument]}` |
| Abstraction | `{"lam":[type,body]}` |
| Equality | `{"equal":[left,right]}` |
| Implication | `{"imp":[antecedent,consequent]}` |

An inference command is `{"infer":{"rule":{ruleName:fields}}}`:

| Rule name | Fields |
| --- | --- |
| `assume`, `refl`, `beta` | `p` |
| `abs` | `name`, `type`, `th` |
| `mkComb`, `trans` | `left`, `right` (theorem indices) |
| `disch` | `p`, `th` |
| `mp` | `implication`, `antecedent` (theorem indices) |
| `symm` | `th` |
| `eqMp` | `equation`, `premise` (theorem indices) |
| `inst` | `replacements` (pairs of terms), `th` |
| `instType` | `substitution`, `th` |
| `subst` | `equations` (term/index pairs), `template`, `th` |

Theory commands have the form `{commandName:fields}`:

| Command name | Fields |
| --- | --- |
| `declareType` | `name` (qualified), `arity` |
| `declareConstant` | `name` (qualified), `type` |
| `defineConstant` | `name` (qualified), `rhs` |
| `defineType` | `name` (qualified), `parameters`, `predicate`, `proof` (index or null) |
| `addAxiom` | `formula` |

## Proof boundary

`FFI.applyCommands_spec` proves that successful transport execution corresponds
to a decoded command sequence and an actual `Execution.run` result.
`FFI.applyCommands_extends` proves theory extension, `FFI.apply_failure` proves
failure leaves the Lean state unchanged, and `FFI.applyCommands_sound` proves
validity of the resulting theorems in every model of the resulting theory.
These declarations are included in the existing axiom audit.

Parsing is runtime code; the JSON tests are executable checks, not additional
logical axioms. No `@[extern]` replaces a verified kernel operation. Lean erases
proof fields in compiled code. The compiler, runtime, C adapter and caller's
memory safety remain outside the Lean proof. JSON serialization fidelity is
covered by behavior tests, not a universal codec roundtrip theorem.
Arbitrary `addAxiom` commands retain only conditional soundness, not consistency.
The existing conservative-execution consistency result applies when no such
commands are used. Input size, execution time and memory use are not bounded
by this ABI; an application requiring isolation should use a separate process.
