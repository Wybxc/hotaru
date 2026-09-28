val article_path = valOf (OS.Process.getEnv "LIST_NOT_NIL_ARTICLE");
val reader_path = valOf (OS.Process.getEnv "LIST_NOT_NIL_HOL4_READER");

fun setting name = let
  val value = valOf (Int.fromString (valOf (OS.Process.getEnv name)))
in
  if value > 0 then value else raise Fail ("invalid " ^ name)
end;

val iterations = setting "LIST_NOT_NIL_ITERATIONS";
val trials = setting "LIST_NOT_NIL_TRIALS";
val warmup = setting "LIST_NOT_NIL_WARMUP";

val _ = load "listTheory";
val _ = load "OpenTheoryReader";
val _ = use reader_path;
val _ = load "metisLib";
val _ = Feedback.set_trace "metis" 0;
open Tactical BasicProvers;

fun const_name name =
  case name of
    ([], "=") => {Thy="min", Name="="}
  | (["HOL4", thy], constant) => {Thy=thy, Name=constant}
  | _ => ListNotNilReader.const_name_in_map name;

fun tyop_name name =
  case name of
    ([], "->") => {Thy="min", Tyop="fun"}
  | ([], "bool") => {Thy="min", Tyop="bool"}
  | (["HOL4", thy], tyop) => {Thy=thy, Tyop=tyop}
  | _ => ListNotNilReader.tyop_name_in_map name;

fun same_sequent (hyps, conclusion) theorem =
  Term.aconv (Thm.concl theorem) conclusion andalso
  HOLset.equal (Thm.hypset theorem,
                HOLset.addList (Term.empty_tmset, hyps));

val encoding_facts = [boolTheory.AND_DEF, boolTheory.EXISTS_DEF,
                      boolTheory.SELECT_AX, boolTheory.FUN_EQ_THM];

fun prove_and_encoding conclusion = let
  val bool_ty = Type.bool
  val p = Term.mk_var ("p", bool_ty)
  val q = Term.mk_var ("q", bool_ty)
  val u = Term.mk_var ("u", bool_ty)
  val v = Term.mk_var ("v", bool_ty)
  val fun_ty = Type.mk_type ("fun", [bool_ty,
    Type.mk_type ("fun", [bool_ty, bool_ty])])
  val f = Term.mk_var ("f", fun_ty)
  val app = Term.mk_comb
  val witness = boolSyntax.mk_forall (f,
    boolSyntax.mk_eq (app (app (f,p),q),
                      app (app (f,boolSyntax.T),boolSyntax.T)))
  val conjunction = boolSyntax.mk_conj (p,q)
  val from_conjunction = Thm.ASSUME conjunction
  val p_eq = Drule.EQT_INTRO (Thm.CONJUNCT1 from_conjunction)
  val q_eq = Drule.EQT_INTRO (Thm.CONJUNCT2 from_conjunction)
  val instantiated = Thm.MK_COMB
    (Thm.MK_COMB (Thm.REFL f, p_eq), q_eq)
  val forward = Thm.DISCH conjunction (Thm.GEN f instantiated)
  val from_witness = Thm.ASSUME witness
  val project_p = Term.mk_abs (u, Term.mk_abs (v,u))
  val project_q = Term.mk_abs (u, Term.mk_abs (v,v))
  val p_th = Drule.EQT_ELIM (Conv.BETA_RULE (Thm.SPEC project_p from_witness))
  val q_th = Drule.EQT_ELIM (Conv.BETA_RULE (Thm.SPEC project_q from_witness))
  val backward = Thm.DISCH witness (Thm.CONJ p_th q_th)
  val pointwise = Thm.GEN p (Thm.GEN q
    (Drule.IMP_ANTISYM_RULE forward backward))
in
  Tactical.prove (conclusion,
    metisLib.METIS_TAC [boolTheory.FUN_EQ_THM, pointwise])
end;

val implication_encoding = Tactical.prove
  (``$==> = (\p q. (p /\ q) = p)``, metisLib.METIS_TAC encoding_facts);
val conjunction_encoding = prove_and_encoding
  ``$/\ = (\p q. (\f:bool->bool->bool. f p q) = (\f. f T T))``;
val exists_encoding = Tactical.prove
  (``$? = (\P:'a->bool. !q. (!x. P x ==> q) ==> q)``,
   metisLib.METIS_TAC encoding_facts);

val approved : (string * Thm.thm) list = [
  ("bool.TRUTH", DB.fetch "bool" "TRUTH"),
  ("derived.IMP_ENCODING", implication_encoding),
  ("bool.FORALL_DEF", DB.fetch "bool" "FORALL_DEF"),
  ("derived.AND_ENCODING", conjunction_encoding),
  ("bool.IMP_ANTISYM_AX", DB.fetch "bool" "IMP_ANTISYM_AX"),
  ("bool.NOT_DEF", DB.fetch "bool" "NOT_DEF"),
  ("bool.EQ_CLAUSES", DB.fetch "bool" "EQ_CLAUSES"),
  ("ConseqConv.NOT_CLAUSES_X", DB.fetch "ConseqConv" "NOT_CLAUSES_X"),
  ("sat.AND_INV2", DB.fetch "sat" "AND_INV2"),
  ("sat.AND_INV_IMP", DB.fetch "sat" "AND_INV_IMP"),
  ("sat.pth_ni1", DB.fetch "sat" "pth_ni1"),
  ("bool.IMP_CLAUSES", DB.fetch "bool" "IMP_CLAUSES"),
  ("sat.pth_ni2", DB.fetch "sat" "pth_ni2"),
  ("sat.OR_DUAL2", DB.fetch "sat" "OR_DUAL2"),
  ("sat.pth_nn", DB.fetch "sat" "pth_nn"),
  ("sat.pth_no1", DB.fetch "sat" "pth_no1"),
  ("sat.OR_DUAL3", DB.fetch "sat" "OR_DUAL3"),
  ("sat.dc_imp", DB.fetch "sat" "dc_imp"),
  ("sat.dc_eq", DB.fetch "sat" "dc_eq"),
  ("sat.pth_no2", DB.fetch "sat" "pth_no2"),
  ("bool.EXISTS_DEF", DB.fetch "bool" "EXISTS_DEF"),
  ("derived.EXISTS_ENCODING", exists_encoding),
  ("bool.OR_DEF", DB.fetch "bool" "OR_DEF"),
  ("bool.SELECT_AX", DB.fetch "bool" "SELECT_AX"),
  ("list.list_CASES", DB.fetch "list" "list_CASES"),
  ("list.TL", DB.fetch "list" "TL"),
  ("list.HD", DB.fetch "list" "HD"),
  ("bool.EQ_REFL", DB.fetch "bool" "EQ_REFL"),
  ("ConseqConv.false_imp", DB.fetch "ConseqConv" "false_imp"),
  ("bool.BOOL_CASES_AX", DB.fetch "bool" "BOOL_CASES_AX"),
  ("list.list_distinct", DB.fetch "list" "list_distinct")
];

val axiom_index = ref 0;
fun approved_axiom _ sequent = let
  val index = !axiom_index
  val (name, theorem) = List.nth (approved, index)
    handle Subscript => raise Fail "article requests too many axioms"
  val _ = if same_sequent sequent theorem then ()
          else raise Fail ("unexpected article axiom at index " ^
                           Int.toString (index + 1) ^ ": " ^ name)
  val _ = axiom_index := index + 1
in
  theorem
end;

fun replay () = let
  val _ = axiom_index := 0
  val result = ListNotNilReader.raw_read_article (TextIO.openIn article_path) {
    define_tyop = fn _ => raise Fail "article attempted to define a type",
    define_const = fn _ => raise Fail "article attempted to define a constant",
    axiom = approved_axiom,
    const_name = const_name,
    tyop_name = tyop_name}
  val _ = if !axiom_index = List.length approved then ()
          else raise Fail "article requested too few axioms"
in
  result
end;

fun check result =
  case Net.listItems result of
    [theorem] =>
      if null (Thm.hyp theorem) andalso
         Term.aconv (Thm.concl theorem) (Thm.concl listTheory.LIST_NOT_NIL)
      then () else raise Fail "replayed LIST_NOT_NIL mismatch"
  | _ => raise Fail "article must export exactly one theorem";

val _ = if List.length approved = 31 then ()
        else raise Fail "incorrect axiom whitelist length";
val _ = List.app (fn (name, theorem) =>
  print ("LIST_NOT_NIL_AXIOM\t" ^ name ^ "\t" ^
         Parse.term_to_string (Thm.concl theorem) ^ "\n")) approved;
val _ = check (replay ());

fun repeat 0 (SOME result) = result
  | repeat 0 NONE = raise Fail "zero article replays"
  | repeat remaining _ = repeat (remaining - 1)
      (SOME (replay ()));

val _ = check (repeat warmup NONE);

fun run_trial trial = let
  val _ = PolyML.fullGC ()
  val start = Time.now ()
  val result = repeat iterations NONE
  val elapsed = Time.toNanoseconds (Time.- (Time.now (), start))
  val _ = check result
  val _ = print ("LIST_NOT_NIL_REPLAY\thol4\t" ^ Int.toString trial ^ "\t" ^
                 Int.toString iterations ^ "\t" ^ LargeInt.toString elapsed ^ "\n")
in
  ()
end;

val _ = List.app run_trial (List.tabulate (trials, fn i => i));
