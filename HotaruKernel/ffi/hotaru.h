#ifndef HOTARU_H
#define HOTARU_H
#include <stddef.h>
#include <stdint.h>
#define HOTARU_API __attribute__((visibility("default")))
#ifdef __cplusplus
extern "C" {
#endif

/* ABI 2: all inputs are borrowed, all output handles/strings are owned.
 * All handle operations run on the initialization OS thread. Output slots must
 * be distinct and must not overlap inputs. On failure, outputs are NULL/zero.
 * Handles must be live, of the declared kind, and obtained from this library. */
typedef struct hotaru_state hotaru_state;
typedef struct hotaru_type hotaru_type;
typedef struct hotaru_term hotaru_term;
typedef struct hotaru_thm hotaru_thm;
typedef struct { const char *data; size_t length; } hotaru_string_view;
typedef struct { hotaru_string_view name; const hotaru_type *type; } hotaru_type_binding;
typedef struct { const hotaru_term *target, *value; } hotaru_term_binding;
typedef struct { const hotaru_term *target; const hotaru_thm *equation; } hotaru_equation;

enum hotaru_status {
    HOTARU_OK = 0,
    HOTARU_INVALID_ARGUMENT = 2, HOTARU_OUT_OF_MEMORY = 3,
    HOTARU_WRONG_THREAD = 4, HOTARU_INIT_FAILED = 5,
    HOTARU_WRONG_KIND = 6, HOTARU_THEORY_MISMATCH = 7, HOTARU_OUT_OF_RANGE = 8,
    HOTARU_INVALID_TYPE = 100, HOTARU_UNBOUND_VARIABLE = 101,
    HOTARU_UNKNOWN_CONSTANT = 102, HOTARU_NOT_FUNCTION = 103,
    HOTARU_TYPE_MISMATCH = 104, HOTARU_NOT_BOOLEAN = 105,
    HOTARU_NOT_EQUATION = 106, HOTARU_NOT_BETA_REDEX = 107,
    HOTARU_FREE_IN_ASSUMPTIONS = 108, HOTARU_NOT_IMPLICATION = 109,
    HOTARU_NOT_VARIABLE = 110, HOTARU_TERM_MISMATCH = 111,
    HOTARU_INVALID_SIGNATURE = 112, HOTARU_DUPLICATE_TYPE = 113,
    HOTARU_DUPLICATE_CONSTANT = 114, HOTARU_FREE_VARIABLES_IN_DEFINITION = 115,
    HOTARU_HIDDEN_TYPE_VARIABLES = 116, HOTARU_DUPLICATE_TYPE_PARAMETER = 117,
    HOTARU_MISSING_NONEMPTY_PROOF = 118, HOTARU_NONEMPTY_PROOF_HAS_ASSUMPTIONS = 119,
    HOTARU_NOT_PREDICATE = 120, HOTARU_INVALID_THEOREM_REFERENCE = 121
};
enum hotaru_type_tag { HOTARU_TYPE_BOOL, HOTARU_TYPE_VAR, HOTARU_TYPE_FN, HOTARU_TYPE_OP };
enum hotaru_term_tag {
    HOTARU_TERM_FREE, HOTARU_TERM_BOUND, HOTARU_TERM_CONST, HOTARU_TERM_APP,
    HOTARU_TERM_LAM, HOTARU_TERM_EQUAL, HOTARU_TERM_IMP
};
enum hotaru_foundation { HOTARU_ETA, HOTARU_SELECTION, HOTARU_INFINITY, HOTARU_BOOL_CASES };

HOTARU_API uint32_t hotaru_abi_version(void);
HOTARU_API const char *hotaru_error_message(int status); /* Static, never free. */
HOTARU_API int hotaru_init(void);
HOTARU_API int hotaru_state_new(hotaru_state **out);
HOTARU_API int hotaru_state_free(hotaru_state *state);
HOTARU_API int hotaru_type_free(hotaru_type *type);
HOTARU_API int hotaru_term_free(hotaru_term *term);
HOTARU_API int hotaru_thm_free(hotaru_thm *thm);
HOTARU_API void hotaru_string_free(char *string); /* May run on any thread. */

/* Structural constructors: types/terms are reusable raw syntax. check and every
 * inference validate them against the supplied theory. Dangling bound variables
 * may occur while constructing a body but are rejected at top level. */
HOTARU_API int hotaru_type_bool(hotaru_type **out);
HOTARU_API int hotaru_type_var(hotaru_string_view name, hotaru_type **out);
HOTARU_API int hotaru_type_fn(const hotaru_type *domain, const hotaru_type *range, hotaru_type **out);
HOTARU_API int hotaru_type_op(hotaru_string_view scope, hotaru_string_view name,
    const hotaru_type *const *args, size_t count, hotaru_type **out);
HOTARU_API int hotaru_term_free_var(hotaru_string_view name, const hotaru_type *type, hotaru_term **out);
HOTARU_API int hotaru_term_bound(uint64_t index, hotaru_term **out);
HOTARU_API int hotaru_term_const(hotaru_string_view scope, hotaru_string_view name,
    const hotaru_type_binding *inst, size_t count, hotaru_term **out);
HOTARU_API int hotaru_term_app(const hotaru_term *function, const hotaru_term *argument, hotaru_term **out);
HOTARU_API int hotaru_term_lam(const hotaru_type *type, const hotaru_term *body, hotaru_term **out);
HOTARU_API int hotaru_term_equal(const hotaru_term *left, const hotaru_term *right, hotaru_term **out);
HOTARU_API int hotaru_term_imp(const hotaru_term *antecedent, const hotaru_term *consequent, hotaru_term **out);
HOTARU_API int hotaru_check(const hotaru_state *state, const hotaru_term *term, hotaru_type **out);

/* Inference never mutates state. Theorem operands must have exactly this owner.
 * Use thm_rebase explicitly to move an ancestor's theorem into an extension. */
HOTARU_API int hotaru_foundation_thm(const hotaru_state *state, uint64_t index, hotaru_thm **out);
HOTARU_API int hotaru_assume(const hotaru_state *state, const hotaru_term *term, hotaru_thm **out);
HOTARU_API int hotaru_refl(const hotaru_state *state, const hotaru_term *term, hotaru_thm **out);
HOTARU_API int hotaru_beta(const hotaru_state *state, const hotaru_term *term, hotaru_thm **out);
HOTARU_API int hotaru_abs(const hotaru_state *state, hotaru_string_view name,
    const hotaru_type *type, const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_mk_comb(const hotaru_state *state, const hotaru_thm *function,
    const hotaru_thm *argument, hotaru_thm **out);
HOTARU_API int hotaru_disch(const hotaru_state *state, const hotaru_term *term,
    const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_mp(const hotaru_state *state, const hotaru_thm *implication,
    const hotaru_thm *antecedent, hotaru_thm **out);
HOTARU_API int hotaru_symm(const hotaru_state *state, const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_trans(const hotaru_state *state, const hotaru_thm *left,
    const hotaru_thm *right, hotaru_thm **out);
HOTARU_API int hotaru_eq_mp(const hotaru_state *state, const hotaru_thm *equation,
    const hotaru_thm *premise, hotaru_thm **out);
HOTARU_API int hotaru_inst(const hotaru_state *state, const hotaru_term_binding *replacements,
    size_t count, const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_inst_type(const hotaru_state *state, const hotaru_type_binding *substitution,
    size_t count, const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_subst(const hotaru_state *state, const hotaru_equation *equations,
    size_t count, const hotaru_term *template_term, const hotaru_thm *thm, hotaru_thm **out);

/* Extensions return new states; the input remains unchanged. Definitions and
 * add_axiom also return a theorem owned by the new state. proof may be NULL to
 * obtain HOTARU_MISSING_NONEMPTY_PROOF after other side conditions are checked. */
HOTARU_API int hotaru_declare_type(const hotaru_state *state, hotaru_string_view scope,
    hotaru_string_view name, uint64_t arity, hotaru_state **out);
HOTARU_API int hotaru_declare_const(const hotaru_state *state, hotaru_string_view scope,
    hotaru_string_view name, const hotaru_type *type, hotaru_state **out);
HOTARU_API int hotaru_define_const(const hotaru_state *state, hotaru_string_view scope,
    hotaru_string_view name, const hotaru_term *rhs, hotaru_state **out, hotaru_thm **definition);
HOTARU_API int hotaru_define_type(const hotaru_state *state, hotaru_string_view scope,
    hotaru_string_view name, const hotaru_string_view *parameters, size_t count,
    const hotaru_term *predicate, const hotaru_thm *proof, hotaru_state **out, hotaru_thm **definition);
HOTARU_API int hotaru_add_axiom(const hotaru_state *state, const hotaru_term *formula,
    hotaru_state **out, hotaru_thm **axiom);
HOTARU_API int hotaru_thm_rebase(const hotaru_state *target, const hotaru_thm *thm, hotaru_thm **out);
HOTARU_API int hotaru_thm_state(const hotaru_thm *thm, hotaru_state **out);

/* Structural inspection: returned children and strings own independent references.
 * Names are UTF-8 byte strings; returned lengths exclude the trailing NUL.
 * Type children: domain/range or operator arguments. Term children: application,
 * equality, implication operands or a lambda body at index 0. */
HOTARU_API int hotaru_type_equal(const hotaru_type *a, const hotaru_type *b, uint8_t *out);
HOTARU_API int hotaru_term_same(const hotaru_term *a, const hotaru_term *b, uint8_t *out);
HOTARU_API int hotaru_type_kind(const hotaru_type *type, uint32_t *out);
HOTARU_API int hotaru_term_kind(const hotaru_term *term, uint32_t *out);
HOTARU_API int hotaru_type_arity(const hotaru_type *type, uint64_t *out);
HOTARU_API int hotaru_type_child(const hotaru_type *type, uint64_t index, hotaru_type **out);
HOTARU_API int hotaru_term_child(const hotaru_term *term, uint64_t index, hotaru_term **out);
HOTARU_API int hotaru_term_annotation(const hotaru_term *term, hotaru_type **out);
HOTARU_API int hotaru_bound_index(const hotaru_term *term, uint64_t *out);
HOTARU_API int hotaru_type_name(const hotaru_type *type, char **out, size_t *length);
HOTARU_API int hotaru_type_scope(const hotaru_type *type, char **out, size_t *length);
HOTARU_API int hotaru_term_name(const hotaru_term *term, char **out, size_t *length);
HOTARU_API int hotaru_term_scope(const hotaru_term *term, char **out, size_t *length);
HOTARU_API int hotaru_inst_count(const hotaru_term *term, uint64_t *out);
HOTARU_API int hotaru_inst_name(const hotaru_term *term, uint64_t index, char **out, size_t *length);
HOTARU_API int hotaru_inst_value(const hotaru_term *term, uint64_t index, hotaru_type **out);
HOTARU_API int hotaru_thm_conclusion(const hotaru_thm *thm, hotaru_term **out);
HOTARU_API int hotaru_thm_assumption_count(const hotaru_thm *thm, uint64_t *out);
HOTARU_API int hotaru_thm_assumption(const hotaru_thm *thm, uint64_t index, hotaru_term **out);

#ifdef __cplusplus
}
#endif
#endif
