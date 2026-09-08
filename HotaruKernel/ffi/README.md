# C handle interface (ABI 2)

The library exposes opaque `hotaru_state`, `hotaru_type`, `hotaru_term`, and
`hotaru_thm` handles. Constructors, inference, theory extensions, and inspection
use C functions directly. ABI 1's JSON commands, numeric theorem references,
`hotaru_apply`, and serialized theorem output have been removed.

## Build and test

From `HotaruKernel/`:

```sh
lake build hotaruC
lake build hotaruCTest
.lake/build/bin/test_hotaru
```

The library is `.lake/build/lib/libhotaru.dylib` on macOS or
`.lake/build/lib/libhotaru.so` on Linux. The public header is `ffi/hotaru.h`.
The build requires the pinned Lean 4.29.0 installation and a system C compiler
with POSIX threads. It embeds a runtime search path to that toolchain.
Distributing the library requires the matching Lean shared libraries and
appropriate loader paths; the library does not contain a standalone runtime.

The first native build compiles the export module's transitive imports.
On macOS, Lake's default linker environment uses a future deployment-version
marker. Set `MACOSX_DEPLOYMENT_TARGET` for a particular deployment target;
generated objects and the matching runtime must support that target too.

`lake build` builds only the implementation. `lake test` includes Lean handle
interface regression proofs using `decide +kernel`. C integration tests remain
an explicit target and CI step. Dependency versions and the lock are unchanged.

## Example

The complete example is [examples/refl.c](examples/refl.c). It constructs a
Boolean variable, proves its reflexive equality, and reads the result as a term
handle. Build it with a regular C compiler:

```sh
cc ffi/examples/refl.c -Iffi -L.lake/build/lib -lhotaru \
  -Wl,-rpath,"$PWD/.lake/build/lib" -o .lake/build/bin/handle_example
.lake/build/bin/handle_example
```

The central calls are:

```c
hotaru_state_new(&state);
hotaru_type_bool(&boolean);
hotaru_term_free_var((hotaru_string_view){"p", 1}, boolean, &p);
hotaru_refl(state, p, &proof);
hotaru_thm_conclusion(proof, &conclusion);
```

Check every return code, as the complete example does.
For Rust, bind these functions with `extern "C"`, represent the opaque objects
as pointers, and use RAII wrappers to call the corresponding free functions.
`hotaru_string_view` and binding arrays have ordinary C struct layouts and can
be represented with `#[repr(C)]`. No Rust code needs Lean's object layout.

## Ownership

Every constructor, inference, accessor returning a handle, and migration returns
an independently owned handle. Inputs are borrowed for the duration of the call.
Release each output with its matching `hotaru_*_free`. NULL frees succeed.
Handles must be live objects of the declared kind from this library; forged
pointers, wrong-kind casts, double frees and use after free are C memory errors.

Terms retain their children, and theorems retain their theory state.
Extensions retain their ancestors. Thus an input may be released while a
result that depends on it is still alive. `hotaru_thm_state` returns an owned
reference to the theorem's state. There is no global mutable current theory.

All handle operations, including frees, must run on the OS thread that first
initializes the library. Other threads receive `HOTARU_WRONG_THREAD`.
Rust handle wrappers should be neither `Send` nor `Sync`; a dedicated worker
thread is another option. Only `hotaru_string_free`, `hotaru_error_message`,
and `hotaru_abi_version` are unrestricted.
This library owns Lean initialization and cannot coexist with a separately
initialized Lean host. The runtime remains initialized until process exit.

## Syntax and checking

Types and terms are reusable raw syntax handles. Constructors do not assert
that a type operator or constant exists in a particular theory. Construct
lambda bodies with de Bruijn bound indices, then call `hotaru_check` on the
completed term to obtain its type. Every inference also runs its existing
kernel checks, so skipping an explicit check cannot bypass side conditions.

Type kinds are Boolean, variable, function and named operator.
Term kinds are free variable, bound variable, constant instance, application,
lambda, equality and implication. Inspect kinds, children, annotations, names,
qualified-name scopes and constant substitutions with the accessor functions.
A lambda has one term child (its body); its argument type is its annotation.
Function types have domain and range children; operator types have argument
children. Leaves have no children. Invalid accessor kinds or indices return
`HOTARU_WRONG_KIND` or `HOTARU_OUT_OF_RANGE`.

Input names are UTF-8 byte views; invalid UTF-8 is rejected. Embedded NUL bytes
are preserved. Output names are allocated, NUL-terminated byte strings with an
explicit length excluding the terminator; release them with
`hotaru_string_free`. A NULL input view is allowed only when its length is zero.
Array pointers may be NULL only when their count is zero.

## Inference and theory identity

All kernel rules have direct entry points, including substitution and type
instantiation. Their theorem operands must belong to exactly the supplied
state. Even separately created but structurally equal theories are distinct.
Inference does not mutate the state, so independent proofs in one theory can
be combined immediately without synchronizing theorem tables.

Declarations and definitions return a new state and leave the original intact.
Definitions also return a theorem owned by that new state. The four foundation
theorems are available through `hotaru_foundation_thm` and the
`hotaru_foundation` enum.

To use an old theorem in a new theory:

```c
hotaru_declare_type(base, scope, name, 0, &extended);
hotaru_thm_rebase(extended, old_proof, &migrated);
hotaru_symm(extended, migrated, &result);
```

Migration accepts only the same state or a descendant along recorded, verified
extensions. It invokes Lean's proved `Thm.rebase` at every extension.
Backward migration, sibling migration and unrelated initial states are rejected.
Directly passing `old_proof` to inference in `extended` is also rejected.
The explicit rule applies to every theorem operand, including substitution
equations and type-definition nonemptiness proofs.

## Errors and proof boundary

Functions return stable numeric status codes declared in the public header.
`hotaru_error_message` returns a static diagnostic string, which must not be
freed. Statuses 100-121 correspond to the existing kernel errors.
Every output is set to NULL or zero on failure; output slots must not alias
each other or input memory. Do not overwrite an owned handle without releasing
it first. A failed operation does not mutate its input state.

`HOTARU_OUT_OF_MEMORY` covers adapter allocations. Runtime allocation failure,
panic or resource exhaustion may terminate the process. This ABI does not
bound input size, memory use or execution time.

`FFI.success_sound` proves soundness of successful theorem results.
`FFI.extension_valid` proves theory-extension and signature invariants.
`FFI.rebase_sound` proves validity after migration. Inference wrappers call
the existing verified kernel operations without foreign replacements.
These declarations and the regression proofs are included in the axiom audit.

The C adapter's pointer ownership, identity checks and argument marshalling,
the compiler, runtime, and caller memory safety remain outside the Lean proof.
C integration tests cover every inference entry point, theory migration,
rejected side conditions, nonempty type definitions, inspection and lifetime
management. Tests do not constitute a proof of the C implementation.
`hotaru_add_axiom` retains conditional soundness only; it does not promise
consistency. The existing model-extension theorems apply to verified
conservative extensions.
