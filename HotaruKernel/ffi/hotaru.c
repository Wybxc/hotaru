#include "hotaru.h"
#include <lean/lean.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

/* These declarations match Lean 4.29.0's generated exports. Object arguments
 * consume one reference. Only this adapter handles the runtime representation. */
extern void lean_initialize(void);
extern lean_object *initialize_HotaruKernel_HotaruKernelFFI(uint8_t builtin);
extern lean_object* hotaru_lean_new(lean_object*);
extern lean_object* hotaru_lean_type_bool(lean_object*);
extern lean_object* hotaru_lean_type_var(lean_object*);
extern lean_object* hotaru_lean_type_fn(lean_object*, lean_object*);
extern lean_object* hotaru_lean_type_op(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_binding(lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_pair(lean_object*, lean_object*);
extern lean_object* hotaru_lean_equation_pair(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_free(lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_bound(uint64_t);
extern lean_object* hotaru_lean_term_const(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_app(lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_lam(lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_equal(lean_object*, lean_object*);
extern lean_object* hotaru_lean_term_imp(lean_object*, lean_object*);
extern lean_object* hotaru_lean_check(lean_object*, lean_object*);
extern lean_object* hotaru_lean_foundation(lean_object*, uint64_t);
extern lean_object* hotaru_lean_assume(lean_object*, lean_object*);
extern lean_object* hotaru_lean_refl(lean_object*, lean_object*);
extern lean_object* hotaru_lean_beta(lean_object*, lean_object*);
extern lean_object* hotaru_lean_abs(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_mk_comb(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_disch(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_mp(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_symm(lean_object*, lean_object*);
extern lean_object* hotaru_lean_trans(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_eq_mp(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_inst(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_inst_type(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_subst(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_extension_state(lean_object*, lean_object*);
extern lean_object* hotaru_lean_extension_thm(lean_object*, lean_object*);
extern lean_object* hotaru_lean_rebase(lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_declare_type(lean_object*, lean_object*, lean_object*, uint64_t);
extern lean_object* hotaru_lean_declare_const(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_define_const(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_define_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* hotaru_lean_add_axiom(lean_object*, lean_object*);
extern lean_object* hotaru_lean_conclusion(lean_object*, lean_object*);
extern uint64_t hotaru_lean_assumption_count(lean_object*, lean_object*);
extern lean_object* hotaru_lean_assumption(lean_object*, lean_object*, uint64_t);
extern uint8_t hotaru_lean_type_eq(lean_object*, lean_object*);
extern uint8_t hotaru_lean_term_eq(lean_object*, lean_object*);
extern uint32_t hotaru_lean_type_kind(lean_object*);
extern uint32_t hotaru_lean_term_kind(lean_object*);
extern lean_object* hotaru_lean_type_name(lean_object*);
extern lean_object* hotaru_lean_type_scope(lean_object*);
extern lean_object* hotaru_lean_term_name(lean_object*);
extern lean_object* hotaru_lean_term_scope(lean_object*);
extern uint64_t hotaru_lean_type_arity(lean_object*);
extern lean_object* hotaru_lean_type_child(lean_object*, uint64_t);
extern lean_object* hotaru_lean_term_child(lean_object*, uint64_t);
extern lean_object* hotaru_lean_term_annotation(lean_object*);
extern lean_object* hotaru_lean_bound_index(lean_object*);
extern lean_object* hotaru_lean_inst_count(lean_object*);
extern lean_object* hotaru_lean_inst_name(lean_object*, uint64_t);
extern lean_object* hotaru_lean_inst_value(lean_object*, uint64_t);

struct hotaru_type { lean_object *value; };
struct hotaru_term { lean_object *value; };
struct hotaru_state {
    lean_object *value;
    lean_object *edge;
    struct hotaru_state *parent;
    size_t references;
};
struct hotaru_thm { lean_object *value; hotaru_state *owner; };
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

uint32_t hotaru_abi_version(void) { return 2; }
int hotaru_init(void) {
    if (pthread_once(&init_once, initialize) != 0) return HOTARU_INIT_FAILED;
    if (!pthread_equal(owner, pthread_self())) return HOTARU_WRONG_THREAD;
    return init_status;
}

#define BEGIN(out, valid) do { \
    if (out) *(out) = 0; \
    if (!(out) || !(valid)) return HOTARU_INVALID_ARGUMENT; \
    int init = hotaru_init(); \
    if (init != HOTARU_OK) return init; \
} while (0)
#define SAME_THEORY(s, th) do { \
    if ((th)->owner != (s)) return HOTARU_THEORY_MISMATCH; \
} while (0)

static lean_object *hold(lean_object *value) { lean_inc(value); return value; }
static hotaru_state *retain_state(const hotaru_state *s) {
    hotaru_state *owned = (hotaru_state *)s;
    ++owned->references;
    return owned;
}
static void release_state(hotaru_state *s) {
    while (s && --s->references == 0) {
        hotaru_state *parent = s->parent;
        lean_dec(s->value);
        if (s->edge) lean_dec(s->edge);
        free(s);
        s = parent;
    }
}

/* Result is Except UInt32 a: error tag 0, success tag 1, one object field. */
static int take_result(lean_object *reply, lean_object **out) {
    int status = HOTARU_OK;
    *out = NULL;
    if (lean_obj_tag(reply) == 0)
        status = (int)lean_unbox_uint32(lean_ctor_get(reply, 0));
    else
        *out = hold(lean_ctor_get(reply, 0));
    lean_dec(reply);
    return status;
}

#define OBJECT_HELPERS(kind) \
static int wrap_##kind(lean_object *value, hotaru_##kind **out) { \
    hotaru_##kind *h = malloc(sizeof(*h)); \
    if (!h) { lean_dec(value); return HOTARU_OUT_OF_MEMORY; } \
    h->value = value; *out = h; return HOTARU_OK; \
} \
static int result_##kind(lean_object *reply, hotaru_##kind **out) { \
    lean_object *value; int status = take_result(reply, &value); \
    return status ? status : wrap_##kind(value, out); \
} \
int hotaru_##kind##_free(hotaru_##kind *h) { \
    if (!h) return HOTARU_OK; \
    int status = hotaru_init(); if (status) return status; \
    lean_dec(h->value); free(h); return HOTARU_OK; \
}
OBJECT_HELPERS(type)
OBJECT_HELPERS(term)

static int wrap_thm(const hotaru_state *s, lean_object *value, hotaru_thm **out) {
    hotaru_thm *th = malloc(sizeof(*th));
    if (!th) { lean_dec(value); return HOTARU_OUT_OF_MEMORY; }
    th->value = value; th->owner = retain_state(s); *out = th;
    return HOTARU_OK;
}
static int result_thm(const hotaru_state *s, lean_object *reply, hotaru_thm **out) {
    lean_object *value;
    int status = take_result(reply, &value);
    return status ? status : wrap_thm(s, value, out);
}
int hotaru_state_new(hotaru_state **out) {
    BEGIN(out, 1);
    hotaru_state *s = calloc(1, sizeof(*s));
    if (!s) return HOTARU_OUT_OF_MEMORY;
    s->value = hotaru_lean_new(lean_box(0)); s->references = 1; *out = s;
    return HOTARU_OK;
}
int hotaru_state_free(hotaru_state *s) {
    if (!s) return HOTARU_OK;
    int status = hotaru_init(); if (status) return status;
    release_state(s); return HOTARU_OK;
}
int hotaru_thm_free(hotaru_thm *th) {
    if (!th) return HOTARU_OK;
    int status = hotaru_init(); if (status) return status;
    lean_dec(th->value); release_state(th->owner); free(th); return HOTARU_OK;
}
int hotaru_thm_state(const hotaru_thm *th, hotaru_state **out) {
    BEGIN(out, th); *out = retain_state(th->owner); return HOTARU_OK;
}
void hotaru_string_free(char *string) { free(string); }

static int make_string(hotaru_string_view s, lean_object **out) {
    *out = NULL;
    if (!s.data && s.length) return HOTARU_INVALID_ARGUMENT;
    const char *data = s.data ? s.data : "";
    lean_object *v = lean_mk_string_from_bytes(data, s.length);
    if (lean_string_size(v) - 1 != s.length ||
        memcmp(lean_string_cstr(v), data, s.length) != 0) {
        lean_dec(v); return HOTARU_INVALID_ARGUMENT;
    }
    *out = v; return HOTARU_OK;
}
static int make_qname(hotaru_string_view scope, hotaru_string_view name,
                      lean_object **ns, lean_object **n) {
    int status = make_string(scope, ns);
    if (status) return status;
    status = make_string(name, n);
    if (status) lean_dec(*ns);
    return status;
}
static int make_bindings(const hotaru_type_binding *xs, size_t count, lean_object **out) {
    lean_object *a = lean_mk_empty_array_with_capacity(lean_usize_to_nat(count));
    for (size_t i = 0; i < count; ++i) {
        lean_object *name;
        if (!xs[i].type) { lean_dec(a); return HOTARU_INVALID_ARGUMENT; }
        int status = make_string(xs[i].name, &name);
        if (status) { lean_dec(a); return status; }
        a = lean_array_push(a, hotaru_lean_binding(name, hold(xs[i].type->value)));
    }
    *out = a; return HOTARU_OK;
}
static int result_string(lean_object *reply, char **out, size_t *length) {
    lean_object *value;
    int status = take_result(reply, &value);
    if (status) return status;
    size_t size = lean_string_size(value);
    char *copy = malloc(size);
    if (!copy) { lean_dec(value); return HOTARU_OUT_OF_MEMORY; }
    memcpy(copy, lean_string_cstr(value), size);
    lean_dec(value); *out = copy; *length = size - 1;
    return HOTARU_OK;
}
static int result_u64(lean_object *reply, uint64_t *out) {
    lean_object *value;
    int status = take_result(reply, &value);
    if (status) return status;
    *out = lean_unbox_uint64(value); lean_dec(value); return HOTARU_OK;
}

int hotaru_type_bool(hotaru_type **out) {
    BEGIN(out, 1); return wrap_type(hotaru_lean_type_bool(lean_box(0)), out);
}
int hotaru_type_var(hotaru_string_view name, hotaru_type **out) {
    BEGIN(out, 1);
    lean_object *n; int status = make_string(name, &n);
    return status ? status : wrap_type(hotaru_lean_type_var(n), out);
}
int hotaru_type_fn(const hotaru_type *a, const hotaru_type *b, hotaru_type **out) {
    BEGIN(out, a && b);
    return wrap_type(hotaru_lean_type_fn(hold(a->value), hold(b->value)), out);
}
int hotaru_type_op(hotaru_string_view scope, hotaru_string_view name,
                    const hotaru_type *const *args, size_t count, hotaru_type **out) {
    BEGIN(out, args || count == 0);
    for (size_t i = 0; i < count; ++i) if (!args[i]) return HOTARU_INVALID_ARGUMENT;
    lean_object *ns, *n; int status = make_qname(scope, name, &ns, &n);
    if (status) return status;
    lean_object *a = lean_mk_empty_array_with_capacity(lean_usize_to_nat(count));
    for (size_t i = 0; i < count; ++i) a = lean_array_push(a, hold(args[i]->value));
    return wrap_type(hotaru_lean_type_op(ns, n, a), out);
}
int hotaru_term_free_var(hotaru_string_view name, const hotaru_type *a, hotaru_term **out) {
    BEGIN(out, a);
    lean_object *n; int status = make_string(name, &n);
    return status ? status : wrap_term(hotaru_lean_term_free(n, hold(a->value)), out);
}
int hotaru_term_bound(uint64_t index, hotaru_term **out) {
    BEGIN(out, 1); return wrap_term(hotaru_lean_term_bound(index), out);
}
int hotaru_term_const(hotaru_string_view scope, hotaru_string_view name,
                      const hotaru_type_binding *xs, size_t count, hotaru_term **out) {
    BEGIN(out, xs || count == 0);
    lean_object *ns, *n, *a; int status = make_qname(scope, name, &ns, &n);
    if (status) return status;
    status = make_bindings(xs, count, &a);
    if (status) { lean_dec(ns); lean_dec(n); return status; }
    return wrap_term(hotaru_lean_term_const(ns, n, a), out);
}
int hotaru_term_lam(const hotaru_type *a, const hotaru_term *p, hotaru_term **out) {
    BEGIN(out, a && p);
    return wrap_term(hotaru_lean_term_lam(hold(a->value), hold(p->value)), out);
}
int hotaru_check(const hotaru_state *s, const hotaru_term *p, hotaru_type **out) {
    BEGIN(out, s && p);
    return result_type(hotaru_lean_check(hold(s->value), hold(p->value)), out);
}
int hotaru_foundation_thm(const hotaru_state *s, uint64_t i, hotaru_thm **out) {
    BEGIN(out, s); return result_thm(s, hotaru_lean_foundation(hold(s->value), i), out);
}
int hotaru_abs(const hotaru_state *s, hotaru_string_view name, const hotaru_type *a,
                const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, s && a && th); SAME_THEORY(s, th);
    lean_object *n; int status = make_string(name, &n);
    return status ? status : result_thm(s,
        hotaru_lean_abs(hold(s->value), n, hold(a->value), hold(th->value)), out);
}
int hotaru_disch(const hotaru_state *s, const hotaru_term *p, const hotaru_thm *th,
                  hotaru_thm **out) {
    BEGIN(out, s && p && th); SAME_THEORY(s, th);
    return result_thm(s, hotaru_lean_disch(hold(s->value), hold(p->value), hold(th->value)), out);
}
int hotaru_symm(const hotaru_state *s, const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, s && th); SAME_THEORY(s, th);
    return result_thm(s, hotaru_lean_symm(hold(s->value), hold(th->value)), out);
}
int hotaru_inst_type(const hotaru_state *s, const hotaru_type_binding *xs, size_t count,
                      const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, s && th && (xs || count == 0)); SAME_THEORY(s, th);
    lean_object *a; int status = make_bindings(xs, count, &a);
    return status ? status : result_thm(s, hotaru_lean_inst_type(hold(s->value), a, hold(th->value)), out);
}
int hotaru_inst(const hotaru_state *s, const hotaru_term_binding *xs, size_t count,
                 const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, s && th && (xs || count == 0)); SAME_THEORY(s, th);
    for (size_t i = 0; i < count; ++i)
        if (!xs[i].target || !xs[i].value) return HOTARU_INVALID_ARGUMENT;
    lean_object *a = lean_mk_empty_array_with_capacity(lean_usize_to_nat(count));
    for (size_t i = 0; i < count; ++i)
        a = lean_array_push(a, hotaru_lean_term_pair(hold(xs[i].target->value), hold(xs[i].value->value)));
    return result_thm(s, hotaru_lean_inst(hold(s->value), a, hold(th->value)), out);
}
int hotaru_subst(const hotaru_state *s, const hotaru_equation *xs, size_t count,
                  const hotaru_term *p, const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, s && p && th && (xs || count == 0)); SAME_THEORY(s, th);
    for (size_t i = 0; i < count; ++i) {
        if (!xs[i].target || !xs[i].equation) return HOTARU_INVALID_ARGUMENT;
        SAME_THEORY(s, xs[i].equation);
    }
    lean_object *a = lean_mk_empty_array_with_capacity(lean_usize_to_nat(count));
    for (size_t i = 0; i < count; ++i)
        a = lean_array_push(a, hotaru_lean_equation_pair(hold(s->value),
            hold(xs[i].target->value), hold(xs[i].equation->value)));
    return result_thm(s, hotaru_lean_subst(hold(s->value), a, hold(p->value), hold(th->value)), out);
}

/* Store each certified extension and retain its parent. This lineage is the
 * only authority for rebasing; structurally equal sibling theories do not mix. */
static int result_extension(const hotaru_state *s, lean_object *reply,
                            hotaru_state **out, hotaru_thm **definition) {
    lean_object *edge;
    int status = take_result(reply, &edge);
    if (status) return status;
    hotaru_state *next = calloc(1, sizeof(*next));
    if (!next) { lean_dec(edge); return HOTARU_OUT_OF_MEMORY; }
    next->references = 1; next->edge = edge; next->parent = retain_state(s);
    next->value = hotaru_lean_extension_state(hold(s->value), hold(edge));
    if (definition) {
        status = result_thm(next, hotaru_lean_extension_thm(hold(s->value), hold(edge)), definition);
        if (status) { release_state(next); return status; }
    }
    *out = next; return HOTARU_OK;
}
int hotaru_declare_type(const hotaru_state *s, hotaru_string_view scope,
                         hotaru_string_view name, uint64_t arity, hotaru_state **out) {
    BEGIN(out, s);
    lean_object *ns, *n; int status = make_qname(scope, name, &ns, &n);
    return status ? status : result_extension(s,
        hotaru_lean_declare_type(hold(s->value), ns, n, arity), out, NULL);
}
int hotaru_declare_const(const hotaru_state *s, hotaru_string_view scope,
                          hotaru_string_view name, const hotaru_type *a, hotaru_state **out) {
    BEGIN(out, s && a);
    lean_object *ns, *n; int status = make_qname(scope, name, &ns, &n);
    return status ? status : result_extension(s,
        hotaru_lean_declare_const(hold(s->value), ns, n, hold(a->value)), out, NULL);
}
int hotaru_define_const(const hotaru_state *s, hotaru_string_view scope,
                         hotaru_string_view name, const hotaru_term *p,
                         hotaru_state **out, hotaru_thm **definition) {
    if (definition) *definition = NULL;
    BEGIN(out, s && p && definition);
    lean_object *ns, *n; int status = make_qname(scope, name, &ns, &n);
    return status ? status : result_extension(s,
        hotaru_lean_define_const(hold(s->value), ns, n, hold(p->value)), out, definition);
}
int hotaru_define_type(const hotaru_state *s, hotaru_string_view scope,
                        hotaru_string_view name, const hotaru_string_view *parameters, size_t count,
                        const hotaru_term *predicate, const hotaru_thm *proof,
                        hotaru_state **out, hotaru_thm **definition) {
    if (definition) *definition = NULL;
    BEGIN(out, s && predicate && definition && (parameters || count == 0));
    if (proof) { SAME_THEORY(s, proof); }
    lean_object *ns, *n; int status = make_qname(scope, name, &ns, &n);
    if (status) return status;
    lean_object *a = lean_mk_empty_array_with_capacity(lean_usize_to_nat(count));
    for (size_t i = 0; i < count; ++i) {
        lean_object *param; status = make_string(parameters[i], &param);
        if (status) { lean_dec(ns); lean_dec(n); lean_dec(a); return status; }
        a = lean_array_push(a, param);
    }
    lean_object *optional = lean_box(0);
    if (proof) {
        optional = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(optional, 0, hold(proof->value));
    }
    return result_extension(s, hotaru_lean_define_type(hold(s->value), ns, n, a,
        hold(predicate->value), optional), out, definition);
}
int hotaru_add_axiom(const hotaru_state *s, const hotaru_term *p,
                      hotaru_state **out, hotaru_thm **axiom) {
    if (axiom) *axiom = NULL;
    BEGIN(out, s && p && axiom);
    return result_extension(s, hotaru_lean_add_axiom(hold(s->value), hold(p->value)), out, axiom);
}
int hotaru_thm_rebase(const hotaru_state *target, const hotaru_thm *th, hotaru_thm **out) {
    BEGIN(out, target && th);
    const hotaru_state *cursor = target;
    size_t count = 0;
    while (cursor && cursor != th->owner) { ++count; cursor = cursor->parent; }
    if (!cursor) return HOTARU_THEORY_MISMATCH;
    if (count > SIZE_MAX / sizeof(hotaru_state *)) return HOTARU_OUT_OF_MEMORY;
    const hotaru_state **path = count ? malloc(count * sizeof(*path)) : NULL;
    if (count && !path) return HOTARU_OUT_OF_MEMORY;
    cursor = target;
    for (size_t i = 0; i < count; ++i) { path[i] = cursor; cursor = cursor->parent; }
    lean_object *value = hold(th->value);
    while (count) {
        const hotaru_state *child = path[--count];
        value = hotaru_lean_rebase(hold(child->parent->value), hold(child->edge), value);
    }
    free(path); return wrap_thm(target, value, out);
}
int hotaru_thm_conclusion(const hotaru_thm *th, hotaru_term **out) {
    BEGIN(out, th);
    return wrap_term(hotaru_lean_conclusion(hold(th->owner->value), hold(th->value)), out);
}
int hotaru_thm_assumption_count(const hotaru_thm *th, uint64_t *out) {
    BEGIN(out, th);
    *out = hotaru_lean_assumption_count(hold(th->owner->value), hold(th->value));
    return HOTARU_OK;
}
int hotaru_thm_assumption(const hotaru_thm *th, uint64_t i, hotaru_term **out) {
    BEGIN(out, th);
    return result_term(hotaru_lean_assumption(hold(th->owner->value), hold(th->value), i), out);
}

int hotaru_term_app(const hotaru_term *a, const hotaru_term *b, hotaru_term **out) {
    BEGIN(out, a && b);
    return wrap_term(hotaru_lean_term_app(hold(a->value), hold(b->value)), out);
}

int hotaru_term_equal(const hotaru_term *a, const hotaru_term *b, hotaru_term **out) {
    BEGIN(out, a && b);
    return wrap_term(hotaru_lean_term_equal(hold(a->value), hold(b->value)), out);
}

int hotaru_term_imp(const hotaru_term *a, const hotaru_term *b, hotaru_term **out) {
    BEGIN(out, a && b);
    return wrap_term(hotaru_lean_term_imp(hold(a->value), hold(b->value)), out);
}

int hotaru_assume(const hotaru_state *s, const hotaru_term *p, hotaru_thm **out) {
    BEGIN(out, s && p);
    return result_thm(s, hotaru_lean_assume(hold(s->value), hold(p->value)), out);
}

int hotaru_refl(const hotaru_state *s, const hotaru_term *p, hotaru_thm **out) {
    BEGIN(out, s && p);
    return result_thm(s, hotaru_lean_refl(hold(s->value), hold(p->value)), out);
}

int hotaru_beta(const hotaru_state *s, const hotaru_term *p, hotaru_thm **out) {
    BEGIN(out, s && p);
    return result_thm(s, hotaru_lean_beta(hold(s->value), hold(p->value)), out);
}

int hotaru_mk_comb(const hotaru_state *s, const hotaru_thm *a, const hotaru_thm *b, hotaru_thm **out) {
    BEGIN(out, s && a && b); SAME_THEORY(s, a); SAME_THEORY(s, b);
    return result_thm(s, hotaru_lean_mk_comb(hold(s->value), hold(a->value), hold(b->value)), out);
}

int hotaru_mp(const hotaru_state *s, const hotaru_thm *a, const hotaru_thm *b, hotaru_thm **out) {
    BEGIN(out, s && a && b); SAME_THEORY(s, a); SAME_THEORY(s, b);
    return result_thm(s, hotaru_lean_mp(hold(s->value), hold(a->value), hold(b->value)), out);
}

int hotaru_trans(const hotaru_state *s, const hotaru_thm *a, const hotaru_thm *b, hotaru_thm **out) {
    BEGIN(out, s && a && b); SAME_THEORY(s, a); SAME_THEORY(s, b);
    return result_thm(s, hotaru_lean_trans(hold(s->value), hold(a->value), hold(b->value)), out);
}

int hotaru_eq_mp(const hotaru_state *s, const hotaru_thm *a, const hotaru_thm *b, hotaru_thm **out) {
    BEGIN(out, s && a && b); SAME_THEORY(s, a); SAME_THEORY(s, b);
    return result_thm(s, hotaru_lean_eq_mp(hold(s->value), hold(a->value), hold(b->value)), out);
}

int hotaru_type_kind(const hotaru_type *h, uint32_t *out) {
    BEGIN(out, h); *out = hotaru_lean_type_kind(hold(h->value)); return HOTARU_OK;
}

int hotaru_term_kind(const hotaru_term *h, uint32_t *out) {
    BEGIN(out, h); *out = hotaru_lean_term_kind(hold(h->value)); return HOTARU_OK;
}

int hotaru_type_arity(const hotaru_type *h, uint64_t *out) {
    BEGIN(out, h); *out = hotaru_lean_type_arity(hold(h->value)); return HOTARU_OK;
}

int hotaru_type_equal(const hotaru_type *a, const hotaru_type *b, uint8_t *out) {
    BEGIN(out, a && b); *out = hotaru_lean_type_eq(hold(a->value), hold(b->value)); return HOTARU_OK;
}

int hotaru_term_same(const hotaru_term *a, const hotaru_term *b, uint8_t *out) {
    BEGIN(out, a && b); *out = hotaru_lean_term_eq(hold(a->value), hold(b->value)); return HOTARU_OK;
}

int hotaru_type_child(const hotaru_type *h, uint64_t index, hotaru_type **out) {
    BEGIN(out, h); return result_type(hotaru_lean_type_child(hold(h->value), index), out);
}

int hotaru_term_child(const hotaru_term *h, uint64_t index, hotaru_term **out) {
    BEGIN(out, h); return result_term(hotaru_lean_term_child(hold(h->value), index), out);
}

int hotaru_term_annotation(const hotaru_term *h, hotaru_type **out) {
    BEGIN(out, h); return result_type(hotaru_lean_term_annotation(hold(h->value)), out);
}

int hotaru_inst_value(const hotaru_term *h, uint64_t index, hotaru_type **out) {
    BEGIN(out, h); return result_type(hotaru_lean_inst_value(hold(h->value), index), out);
}

int hotaru_bound_index(const hotaru_term *h, uint64_t *out) {
    BEGIN(out, h); return result_u64(hotaru_lean_bound_index(hold(h->value)), out);
}

int hotaru_inst_count(const hotaru_term *h, uint64_t *out) {
    BEGIN(out, h); return result_u64(hotaru_lean_inst_count(hold(h->value)), out);
}

int hotaru_type_name(const hotaru_type *h, char **out, size_t *length) {
    if (length) *length = 0;
    BEGIN(out, h && length);
    return result_string(hotaru_lean_type_name(hold(h->value)), out, length);
}

int hotaru_type_scope(const hotaru_type *h, char **out, size_t *length) {
    if (length) *length = 0;
    BEGIN(out, h && length);
    return result_string(hotaru_lean_type_scope(hold(h->value)), out, length);
}

int hotaru_term_name(const hotaru_term *h, char **out, size_t *length) {
    if (length) *length = 0;
    BEGIN(out, h && length);
    return result_string(hotaru_lean_term_name(hold(h->value)), out, length);
}

int hotaru_term_scope(const hotaru_term *h, char **out, size_t *length) {
    if (length) *length = 0;
    BEGIN(out, h && length);
    return result_string(hotaru_lean_term_scope(hold(h->value)), out, length);
}

int hotaru_inst_name(const hotaru_term *h, uint64_t index, char **out, size_t *length) {
    if (length) *length = 0;
    BEGIN(out, h && length);
    return result_string(hotaru_lean_inst_name(hold(h->value), index), out, length);
}

const char *hotaru_error_message(int status) {
    static const char *const kernel[] = {
        "invalid type", "unbound variable", "unknown constant", "not a function",
        "type mismatch", "not boolean", "not an equation", "not a beta redex",
        "free in assumptions", "not an implication", "not a variable", "term mismatch",
        "invalid signature", "duplicate type", "duplicate constant", "free variables in definition",
        "hidden type variables", "duplicate type parameter", "missing nonempty proof",
        "nonempty proof has assumptions", "not a predicate", "invalid theorem reference"
    };
    if (status >= 100 && status <= 121) return kernel[status - 100];
    switch (status) {
        case HOTARU_OK: return "success";
        case HOTARU_INVALID_ARGUMENT: return "invalid argument or UTF-8";
        case HOTARU_OUT_OF_MEMORY: return "out of memory";
        case HOTARU_WRONG_THREAD: return "wrong thread";
        case HOTARU_INIT_FAILED: return "Lean initialization failed";
        case HOTARU_WRONG_KIND: return "wrong syntax kind for this accessor";
        case HOTARU_THEORY_MISMATCH: return "theorem belongs to another theory";
        case HOTARU_OUT_OF_RANGE: return "index out of range";
        default: return "unknown error";
    }
}
