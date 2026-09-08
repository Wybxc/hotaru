#ifndef HOTARU_H
#define HOTARU_H

#include <stddef.h>
#include <stdint.h>

#if defined(_WIN32)
#define HOTARU_API __declspec(dllexport)
#else
#define HOTARU_API __attribute__((visibility("default")))
#endif

#ifdef __cplusplus
extern "C" {
#endif

typedef struct hotaru_state hotaru_state;

enum hotaru_status {
    HOTARU_OK = 0,
    HOTARU_REJECTED = 1,
    HOTARU_INVALID_ARGUMENT = 2,
    HOTARU_OUT_OF_MEMORY = 3,
    HOTARU_WRONG_THREAD = 4,
    HOTARU_INIT_FAILED = 5
};

/* ABI version, independent of the Lean runtime version. */
HOTARU_API uint32_t hotaru_abi_version(void);

/* Initialize once, on the OS thread used for all state operations.
 * This library owns Lean initialization; do not combine with another Lean host.
 * Supported platforms: macOS and Linux. No runtime shutdown is required. */
HOTARU_API int hotaru_init(void);
HOTARU_API int hotaru_state_new(hotaru_state **out);

/* Borrow state and UTF-8 JSON bytes for this call. Commands are a JSON array.
 * On success, out receives a new immutable state; state remains usable.
 * On rejection, out is NULL and response contains a JSON error.
 * For other failures, both outputs are NULL. Output pointers must be distinct.
 * Release every returned response with hotaru_string_free.
 * Theorem indices in commands are local to the supplied state. */
HOTARU_API int hotaru_apply(const hotaru_state *state,
                          const char *commands, size_t length,
                          hotaru_state **out, char **response);

/* Return a sequent as JSON, or HOTARU_REJECTED and a JSON error.
 * Returned sequents are data, never accepted as certified theorem imports. */
HOTARU_API int hotaru_theorem(const hotaru_state *state, uint64_t index,
                            char **response);

/* NULL is allowed. Free each owned state once, on the initialization thread. */
HOTARU_API int hotaru_state_free(hotaru_state *state);
/* Strings use ordinary C allocation and may be freed on any thread. */
HOTARU_API void hotaru_string_free(char *string);

#ifdef __cplusplus
}
#endif
#endif
