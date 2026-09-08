#include "hotaru.h"
#include <stdio.h>

int main(void) {
    hotaru_state *state = NULL;
    hotaru_type *boolean = NULL;
    hotaru_term *p = NULL, *conclusion = NULL, *left = NULL;
    hotaru_thm *proof = NULL;
    int status = HOTARU_OK;
    uint8_t same = 0;
    uint32_t kind = 0;
#define TRY(call) do { status = (call); if (status) goto cleanup; } while (0)
    TRY(hotaru_state_new(&state));
    TRY(hotaru_type_bool(&boolean));
    TRY(hotaru_term_free_var((hotaru_string_view){"p", 1}, boolean, &p));
    TRY(hotaru_refl(state, p, &proof));
    TRY(hotaru_thm_conclusion(proof, &conclusion));
    TRY(hotaru_term_kind(conclusion, &kind));
    TRY(hotaru_term_child(conclusion, 0, &left));
    TRY(hotaru_term_same(left, p, &same));
    printf("Equality: %s; left operand is p: %s\n",
           kind == HOTARU_TERM_EQUAL ? "yes" : "no", same ? "yes" : "no");
cleanup:
    hotaru_term_free(left);
    hotaru_term_free(conclusion);
    hotaru_thm_free(proof);
    hotaru_term_free(p);
    hotaru_type_free(boolean);
    hotaru_state_free(state);
    if (status) fprintf(stderr, "%s\n", hotaru_error_message(status));
    return status ? 1 : 0;
}
