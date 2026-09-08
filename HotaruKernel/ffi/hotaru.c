#include "hotaru.h"
#include <lean/lean.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

/* Signatures match the generated C for the pinned Lean 4.29.0 toolchain.
 * Exported object arguments consume one reference, including accessors. */
extern void lean_initialize(void);
extern lean_object *initialize_HotaruKernel_HotaruKernelFFI(uint8_t builtin);
extern lean_object *hotaru_lean_new(lean_object *unit);
extern lean_object *hotaru_lean_apply(lean_object *state, lean_object *input);
extern lean_object *hotaru_lean_theorem(lean_object *state, uint64_t index);
extern lean_object *hotaru_lean_response_state(lean_object *response);
extern uint8_t hotaru_lean_response_success(lean_object *response);
extern lean_object *hotaru_lean_response_json(lean_object *response);

struct hotaru_state { lean_object *value; };
static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static pthread_t owner;
static int init_status = HOTARU_INIT_FAILED;

static void initialize(void) {
    owner = pthread_self();
    lean_initialize();
    lean_object *result = initialize_HotaruKernel_HotaruKernelFFI(1);
    if (lean_io_result_is_ok(result)) init_status = HOTARU_OK;
    lean_dec(result);
    lean_io_mark_end_initialization();
}

uint32_t hotaru_abi_version(void) { return 1; }

int hotaru_init(void) {
    if (pthread_once(&init_once, initialize) != 0) return HOTARU_INIT_FAILED;
    if (!pthread_equal(owner, pthread_self())) return HOTARU_WRONG_THREAD;
    return init_status;
}

static int copy_response(lean_object *reply, char **out) {
    lean_inc(reply);
    int status = hotaru_lean_response_success(reply) ? HOTARU_OK : HOTARU_REJECTED;
    lean_inc(reply);
    lean_object *json = hotaru_lean_response_json(reply);
    size_t size = lean_string_size(json);
    char *copy = malloc(size);
    if (copy) memcpy(copy, lean_string_cstr(json), size);
    lean_dec(json);
    *out = copy;
    return copy ? status : HOTARU_OUT_OF_MEMORY;
}

int hotaru_state_new(hotaru_state **out) {
    if (!out) return HOTARU_INVALID_ARGUMENT;
    *out = NULL;
    int status = hotaru_init();
    if (status != HOTARU_OK) return status;
    hotaru_state *state = malloc(sizeof(*state));
    if (!state) return HOTARU_OUT_OF_MEMORY;
    state->value = hotaru_lean_new(lean_box(0));
    *out = state;
    return HOTARU_OK;
}

int hotaru_apply(const hotaru_state *state, const char *commands, size_t length,
                 hotaru_state **out, char **response) {
    if (out) *out = NULL;
    if (response) *response = NULL;
    if (!state || !commands || !out || !response) return HOTARU_INVALID_ARGUMENT;
    int status = hotaru_init();
    if (status != HOTARU_OK) return status;
    lean_object *input = lean_mk_string_from_bytes(commands, length);
    /* The runtime repairs invalid UTF-8. Reject repairs at the transport boundary. */
    if (lean_string_size(input) - 1 != length ||
        memcmp(lean_string_cstr(input), commands, length) != 0) {
        lean_dec(input);
        return HOTARU_INVALID_ARGUMENT;
    }
    lean_inc(state->value);
    lean_object *reply = hotaru_lean_apply(state->value, input);
    status = copy_response(reply, response);
    if (status == HOTARU_OK) {
        hotaru_state *next = malloc(sizeof(*next));
        if (next) {
            lean_inc(reply);
            next->value = hotaru_lean_response_state(reply);
            *out = next;
        } else {
            free(*response);
            *response = NULL;
            status = HOTARU_OUT_OF_MEMORY;
        }
    }
    lean_dec(reply);
    return status;
}

int hotaru_theorem(const hotaru_state *state, uint64_t index, char **response) {
    if (response) *response = NULL;
    if (!state || !response) return HOTARU_INVALID_ARGUMENT;
    int status = hotaru_init();
    if (status != HOTARU_OK) return status;
    lean_inc(state->value);
    lean_object *reply = hotaru_lean_theorem(state->value, index);
    status = copy_response(reply, response);
    lean_dec(reply);
    return status;
}

int hotaru_state_free(hotaru_state *state) {
    if (!state) return HOTARU_OK;
    int status = hotaru_init();
    if (status != HOTARU_OK) return status;
    lean_dec(state->value);
    free(state);
    return HOTARU_OK;
}

void hotaru_string_free(char *string) { free(string); }
