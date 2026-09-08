#include "hotaru.h"
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>

#define S(text) ((hotaru_string_view){text, sizeof(text) - 1})
#define EXPECT(expected, call) do { \
    int hotaru_test_status_ = (call); \
    if (hotaru_test_status_ != (expected)) { \
        fprintf(stderr, "%s: expected %d, got %d (%s) at line %d\n", \
                #call, (expected), hotaru_test_status_, \
                hotaru_error_message(hotaru_test_status_), __LINE__); \
        assert(hotaru_test_status_ == (expected)); \
    } \
} while (0)
#define OK(call) EXPECT(HOTARU_OK, call)
#define TYPE(name, call) hotaru_type *name = NULL; OK(call); types[nt++] = name
#define TERM(name, call) hotaru_term *name = NULL; OK(call); terms[np++] = name
#define THM(name, call) hotaru_thm *name = NULL; OK(call); thms[nh++] = name
#define STATE(name, call) hotaru_state *name = NULL; OK(call); states[ns++] = name

static void same_term(const hotaru_term *a, const hotaru_term *b) {
    uint8_t same = 0; OK(hotaru_term_same(a, b, &same)); assert(same);
}
static void same_type(const hotaru_type *a, const hotaru_type *b) {
    uint8_t same = 0; OK(hotaru_type_equal(a, b, &same)); assert(same);
}
static void has_conclusion(const hotaru_thm *th, const hotaru_term *expected) {
    hotaru_term *actual = NULL; OK(hotaru_thm_conclusion(th, &actual));
    same_term(actual, expected); OK(hotaru_term_free(actual));
}
static void *wrong_thread(void *arg) {
    hotaru_state *s = arg;
    hotaru_thm *th = NULL;
    EXPECT(HOTARU_WRONG_THREAD, hotaru_init());
    EXPECT(HOTARU_WRONG_THREAD, hotaru_foundation_thm(s, 0, &th));
    assert(th == NULL);
    EXPECT(HOTARU_WRONG_THREAD, hotaru_state_free(s));
    hotaru_type *b = NULL;
    EXPECT(HOTARU_WRONG_THREAD, hotaru_type_bool(&b)); assert(b == NULL);
    return NULL;
}

int main(void) {
    hotaru_type *types[64]; size_t nt = 0;
    hotaru_term *terms[128]; size_t np = 0;
    hotaru_thm *thms[128]; size_t nh = 0;
    hotaru_state *states[32]; size_t ns = 0;
    assert(hotaru_abi_version() == 2);
    OK(hotaru_init()); OK(hotaru_init());
    EXPECT(HOTARU_INVALID_ARGUMENT, hotaru_state_new(NULL));
    STATE(base, hotaru_state_new(&base));
    STATE(other, hotaru_state_new(&other));
    TYPE(b, hotaru_type_bool(&b));
    TYPE(a, hotaru_type_var(S("a"), &a));
    TYPE(bb, hotaru_type_fn(b, b, &bb));
    TYPE(aa, hotaru_type_fn(a, a, &aa));
    TERM(p, hotaru_term_free_var(S("p"), b, &p));
    TERM(q, hotaru_term_free_var(S("q"), b, &q));
    TERM(xa, hotaru_term_free_var(S("x"), a, &xa));
    TERM(xb, hotaru_term_free_var(S("x"), b, &xb));
    TERM(v0, hotaru_term_bound(0, &v0));
    TERM(id, hotaru_term_lam(b, v0, &id));
    TERM(app, hotaru_term_app(id, p, &app));
    TERM(eqpp, hotaru_term_equal(p, p, &eqpp));
    TERM(eqqq, hotaru_term_equal(q, q, &eqqq));
    TERM(imppp, hotaru_term_imp(p, p, &imppp));
    TYPE(checked, hotaru_check(base, id, &checked)); same_type(checked, bb);
    THM(rp, hotaru_refl(base, p, &rp)); has_conclusion(rp, eqpp);
    THM(ap, hotaru_assume(base, p, &ap)); has_conclusion(ap, p);
    THM(bt, hotaru_beta(base, app, &bt));
    THM(abstract, hotaru_abs(base, S("p"), b, rp, &abstract));
    THM(ri, hotaru_refl(base, id, &ri));
    THM(comb, hotaru_mk_comb(base, ri, rp, &comb));
    THM(dis, hotaru_disch(base, p, ap, &dis)); has_conclusion(dis, imppp);
    THM(mp, hotaru_mp(base, dis, ap, &mp)); has_conclusion(mp, p);
    THM(sym, hotaru_symm(base, rp, &sym)); has_conclusion(sym, eqpp);
    THM(trans, hotaru_trans(base, rp, sym, &trans)); has_conclusion(trans, eqpp);
    THM(eqmp, hotaru_eq_mp(base, rp, ap, &eqmp)); has_conclusion(eqmp, p);
    hotaru_term_binding replace[] = {{p, q}};
    THM(inst, hotaru_inst(base, replace, 1, rp, &inst)); has_conclusion(inst, eqqq);
    THM(rx, hotaru_refl(base, xa, &rx));
    hotaru_type_binding bindings[] = {{S("a"), b}};
    THM(itype, hotaru_inst_type(base, bindings, 1, rx, &itype));
    TERM(eqxx, hotaru_term_equal(xb, xb, &eqxx)); has_conclusion(itype, eqxx);
    THM(rxb, hotaru_refl(base, xb, &rxb));
    THM(before_merge, hotaru_abs(base, S("x"), a, rxb, &before_merge));
    THM(after_merge, hotaru_inst_type(base, bindings, 1, before_merge, &after_merge));
    TERM(free_under_lambda, hotaru_term_lam(b, xb, &free_under_lambda));
    TERM(uncaptured, hotaru_term_equal(free_under_lambda, free_under_lambda, &uncaptured));
    has_conclusion(after_merge, uncaptured);
    TERM(v1, hotaru_term_bound(1, &v1));
    TERM(inner, hotaru_term_lam(b, v1, &inner));
    TERM(outer, hotaru_term_lam(b, inner, &outer));
    TERM(nested_app, hotaru_term_app(outer, p, &nested_app));
    TERM(nested_result, hotaru_term_lam(b, p, &nested_result));
    TERM(nested_equation, hotaru_term_equal(nested_app, nested_result, &nested_equation));
    THM(nested_beta, hotaru_beta(base, nested_app, &nested_beta));
    has_conclusion(nested_beta, nested_equation);
    hotaru_equation equations[] = {{p, rp}};
    THM(subst, hotaru_subst(base, equations, 1, p, ap, &subst)); has_conclusion(subst, p);
    for (uint64_t i = 0; i < 4; ++i) {
        hotaru_thm *th; OK(hotaru_foundation_thm(base, i, &th)); OK(hotaru_thm_free(th));
    }

    hotaru_thm *bad = NULL; hotaru_type *bad_type = NULL; hotaru_term *bad_term = NULL;
    hotaru_state *bad_state = NULL;
    EXPECT(HOTARU_OUT_OF_RANGE, hotaru_foundation_thm(base, UINT64_MAX, &bad));
    EXPECT(HOTARU_NOT_BOOLEAN, hotaru_assume(base, id, &bad));
    EXPECT(HOTARU_UNBOUND_VARIABLE, hotaru_refl(base, v0, &bad));
    EXPECT(HOTARU_NOT_BETA_REDEX, hotaru_beta(base, p, &bad));
    EXPECT(HOTARU_NOT_FUNCTION, hotaru_mk_comb(base, rp, rp, &bad));
    EXPECT(HOTARU_NOT_IMPLICATION, hotaru_mp(base, rp, ap, &bad));
    EXPECT(HOTARU_NOT_EQUATION, hotaru_symm(base, ap, &bad));
    THM(aeq, hotaru_assume(base, eqpp, &aeq));
    EXPECT(HOTARU_FREE_IN_ASSUMPTIONS, hotaru_abs(base, S("p"), b, aeq, &bad));
    TERM(bad_app, hotaru_term_app(p, q, &bad_app));
    EXPECT(HOTARU_NOT_FUNCTION, hotaru_check(base, bad_app, &bad_type));
    TERM(unknown, hotaru_term_const(S("test"), S("missing"), NULL, 0, &unknown));
    EXPECT(HOTARU_UNKNOWN_CONSTANT, hotaru_refl(base, unknown, &bad));
    EXPECT(HOTARU_INVALID_ARGUMENT, hotaru_inst(base, NULL, 1, rp, &bad));
    EXPECT(HOTARU_INVALID_ARGUMENT, hotaru_type_var(S("\xff"), &bad_type));
    hotaru_type_binding invalid_bindings[] = {{S("a"), b}, {S("\xff"), b}};
    EXPECT(HOTARU_INVALID_ARGUMENT, hotaru_inst_type(base, invalid_bindings, 2, rp, &bad));
    EXPECT(HOTARU_INVALID_ARGUMENT,
        hotaru_term_const(S("test"), S("\xff"), NULL, 0, &bad_term));
    assert(!bad && !bad_type);
    TYPE(unknown_type, hotaru_type_op(S("test"), S("missing"), NULL, 0, &unknown_type));
    TERM(unknown_var, hotaru_term_free_var(S("u"), unknown_type, &unknown_var));
    EXPECT(HOTARU_INVALID_TYPE, hotaru_check(base, unknown_var, &bad_type));

    /* Inspect the syntax directly, including exact UTF-8 byte names. */
    uint32_t kind; uint64_t number; char *text = NULL; size_t length;
    OK(hotaru_type_kind(bb, &kind)); assert(kind == HOTARU_TYPE_FN);
    OK(hotaru_term_kind(app, &kind)); assert(kind == HOTARU_TERM_APP);
    OK(hotaru_type_arity(bb, &number)); assert(number == 2);
    TYPE(domain, hotaru_type_child(bb, 0, &domain)); same_type(domain, b);
    TERM(body, hotaru_term_child(id, 0, &body)); same_term(body, v0);
    TYPE(annotation, hotaru_term_annotation(p, &annotation)); same_type(annotation, b);
    OK(hotaru_bound_index(v0, &number)); assert(number == 0);
    EXPECT(HOTARU_WRONG_KIND, hotaru_bound_index(p, &number)); assert(number == 0);
    EXPECT(HOTARU_OUT_OF_RANGE, hotaru_term_child(id, 1, &bad_term)); assert(!bad_term);
    EXPECT(HOTARU_WRONG_KIND, hotaru_term_annotation(app, &bad_type));
    OK(hotaru_type_name(a, &text, &length)); assert(length == 1 && text[0] == 'a');
    hotaru_string_free(text);
    TERM(nul_name, hotaru_term_free_var(S("a\0b"), b, &nul_name));
    OK(hotaru_term_name(nul_name, &text, &length));
    assert(length == 3 && memcmp(text, "a\0b", 3) == 0); hotaru_string_free(text);
    OK(hotaru_thm_assumption_count(ap, &number)); assert(number == 1);
    TERM(hyp, hotaru_thm_assumption(ap, 0, &hyp)); same_term(hyp, p);
    EXPECT(HOTARU_OUT_OF_RANGE, hotaru_thm_assumption(ap, 1, &bad_term));
    OK(hotaru_thm_assumption_count(rp, &number)); assert(number == 0);

    /* Independent branches cannot exchange theorem handles implicitly. */
    THM(foreign, hotaru_refl(other, p, &foreign));
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_trans(base, rp, foreign, &bad));
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_thm_rebase(base, foreign, &bad));
    STATE(poly, hotaru_declare_const(base, S("test"), S("poly"), aa, &poly));
    STATE(sibling, hotaru_declare_const(base, S("test"), S("poly"), aa, &sibling));
    TERM(pc, hotaru_term_const(S("test"), S("poly"), bindings, 1, &pc));
    TYPE(pc_type, hotaru_check(poly, pc, &pc_type)); same_type(pc_type, bb);
    EXPECT(HOTARU_UNKNOWN_CONSTANT, hotaru_check(base, pc, &bad_type));
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_symm(poly, rp, &bad));
    THM(migrated, hotaru_thm_rebase(poly, rp, &migrated)); has_conclusion(migrated, eqpp);
    THM(migrated_sym, hotaru_symm(poly, migrated, &migrated_sym));
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_thm_rebase(sibling, migrated, &bad));
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_thm_rebase(base, migrated, &bad));
    hotaru_equation foreign_eq[] = {{p, migrated}};
    EXPECT(HOTARU_THEORY_MISMATCH, hotaru_subst(base, foreign_eq, 1, p, ap, &bad));
    OK(hotaru_term_scope(pc, &text, &length)); assert(length == 4 && !memcmp(text, "test", 4));
    hotaru_string_free(text);
    OK(hotaru_inst_count(pc, &number)); assert(number == 1);
    OK(hotaru_inst_name(pc, 0, &text, &length)); assert(length == 1 && text[0] == 'a');
    hotaru_string_free(text);
    TYPE(inst_value, hotaru_inst_value(pc, 0, &inst_value)); same_type(inst_value, b);
    EXPECT(HOTARU_WRONG_KIND, hotaru_inst_count(p, &number));
    EXPECT(HOTARU_OUT_OF_RANGE, hotaru_inst_value(pc, 1, &bad_type));
    STATE(box, hotaru_declare_type(poly, S("test"), S("box"), 1, &box));
    THM(twice, hotaru_thm_rebase(box, rp, &twice)); has_conclusion(twice, eqpp);
    const hotaru_type *args[] = {b};
    TYPE(box_type, hotaru_type_op(S("test"), S("box"), args, 1, &box_type));
    TERM(box_var, hotaru_term_free_var(S("u"), box_type, &box_var));
    TYPE(box_checked, hotaru_check(box, box_var, &box_checked)); same_type(box_checked, box_type);
    TYPE(wrong_arity, hotaru_type_op(S("test"), S("box"), NULL, 0, &wrong_arity));
    TERM(wrong_var, hotaru_term_free_var(S("u"), wrong_arity, &wrong_var));
    EXPECT(HOTARU_INVALID_TYPE, hotaru_check(box, wrong_var, &bad_type));
    OK(hotaru_type_scope(box_type, &text, &length)); assert(length == 4);
    hotaru_string_free(text);
    EXPECT(HOTARU_DUPLICATE_TYPE, hotaru_declare_type(box, S("test"), S("box"), 1, &bad_state));
    EXPECT(HOTARU_DUPLICATE_CONSTANT, hotaru_declare_const(poly, S("test"), S("poly"), aa, &bad_state));

    hotaru_state *defined = NULL; hotaru_thm *definition = NULL;
    EXPECT(HOTARU_FREE_VARIABLES_IN_DEFINITION,
        hotaru_define_const(base, S("test"), S("bad"), p, &bad_state, &bad));
    assert(!bad_state && !bad);
    OK(hotaru_define_const(base, S("test"), S("id"), id, &defined, &definition));
    OK(hotaru_state_free(defined)); /* The theorem retains its owner. */
    STATE(recovered, hotaru_thm_state(definition, &recovered));
    TERM(def_formula, hotaru_thm_conclusion(definition, &def_formula));
    OK(hotaru_thm_free(definition));
    TERM(def_constant, hotaru_term_child(def_formula, 0, &def_constant));
    TYPE(def_type, hotaru_check(recovered, def_constant, &def_type)); same_type(def_type, bb);

    /* Construct a genuine nonemptiness proof using only exported inference. */
    TERM(truth, hotaru_term_equal(id, id, &truth));
    TERM(pred, hotaru_term_lam(b, truth, &pred));
    TERM(falsehood, hotaru_term_equal(id, pred, &falsehood));
    TERM(empty, hotaru_term_lam(b, falsehood, &empty));
    TERM(pred_eq, hotaru_term_equal(pred, empty, &pred_eq));
    TERM(exists, hotaru_term_imp(pred_eq, falsehood, &exists));
    THM(eq_assumption, hotaru_assume(base, pred_eq, &eq_assumption));
    THM(truth_refl, hotaru_refl(base, truth, &truth_refl));
    THM(applied, hotaru_mk_comb(base, eq_assumption, truth_refl, &applied));
    TERM(left_app, hotaru_term_app(pred, truth, &left_app));
    TERM(right_app, hotaru_term_app(empty, truth, &right_app));
    THM(left_beta, hotaru_beta(base, left_app, &left_beta));
    THM(right_beta, hotaru_beta(base, right_app, &right_beta));
    THM(left_symm, hotaru_symm(base, left_beta, &left_symm));
    THM(chain, hotaru_trans(base, left_symm, applied, &chain));
    THM(chain2, hotaru_trans(base, chain, right_beta, &chain2));
    THM(contradiction, hotaru_eq_mp(base, chain2, ri, &contradiction));
    THM(nonempty, hotaru_disch(base, pred_eq, contradiction, &nonempty));
    has_conclusion(nonempty, exists);
    EXPECT(HOTARU_MISSING_NONEMPTY_PROOF,
        hotaru_define_type(base, S("test"), S("inhabited"), NULL, 0, pred, NULL, &bad_state, &bad));
    EXPECT(HOTARU_THEORY_MISMATCH,
        hotaru_define_type(poly, S("test"), S("inhabited"), NULL, 0, pred, nonempty, &bad_state, &bad));
    hotaru_string_view duplicate_params[] = {S("a"), S("a")};
    EXPECT(HOTARU_DUPLICATE_TYPE_PARAMETER,
        hotaru_define_type(base, S("test"), S("inhabited"), duplicate_params, 2, pred, nonempty,
                           &bad_state, &bad));
    hotaru_state *inhabited = NULL; hotaru_thm *type_def = NULL;
    OK(hotaru_define_type(base, S("test"), S("inhabited"), NULL, 0, pred, nonempty,
                          &inhabited, &type_def));
    states[ns++] = inhabited; thms[nh++] = type_def;
    TYPE(inhabited_type, hotaru_type_op(S("test"), S("inhabited"), NULL, 0, &inhabited_type));
    TERM(inhabited_var, hotaru_term_free_var(S("v"), inhabited_type, &inhabited_var));
    TYPE(inhabited_checked, hotaru_check(inhabited, inhabited_var, &inhabited_checked));

    hotaru_state *axioms = NULL; hotaru_thm *axiom = NULL;
    OK(hotaru_add_axiom(base, p, &axioms, &axiom));
    states[ns++] = axioms; thms[nh++] = axiom;
    has_conclusion(axiom, p);
    OK(hotaru_thm_assumption_count(axiom, &number)); assert(number == 0);

    pthread_t thread;
    assert(pthread_create(&thread, NULL, wrong_thread, base) == 0);
    assert(pthread_join(thread, NULL) == 0);
    for (int i = 0; i < 100; ++i) {
        hotaru_thm *copy = NULL; hotaru_term *value = NULL;
        OK(hotaru_thm_rebase(box, rp, &copy)); OK(hotaru_thm_conclusion(copy, &value));
        OK(hotaru_thm_free(copy)); same_term(value, eqpp); OK(hotaru_term_free(value));
    }
    /* Release inputs before outputs: each result owns the references it needs. */
    while (ns) OK(hotaru_state_free(states[--ns]));
    while (nt) OK(hotaru_type_free(types[--nt]));
    while (np) OK(hotaru_term_free(terms[--np]));
    TERM(last, hotaru_thm_conclusion(rp, &last)); OK(hotaru_term_free(last)); --np;
    while (nh) OK(hotaru_thm_free(thms[--nh]));
    OK(hotaru_state_free(NULL)); OK(hotaru_type_free(NULL));
    OK(hotaru_term_free(NULL)); OK(hotaru_thm_free(NULL)); hotaru_string_free(NULL);
    puts("C handle ABI tests passed");
    return 0;
}
