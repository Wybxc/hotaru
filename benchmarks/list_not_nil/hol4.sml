val marker = "LIST_NOT_NIL_BENCH";

fun setting name =
  let
    val value = valOf (Int.fromString (valOf (OS.Process.getEnv name)))
  in
    if value > 0 then value else raise Fail ("invalid " ^ name)
  end;

val iterations = setting "LIST_NOT_NIL_ITERATIONS";
val trials = setting "LIST_NOT_NIL_TRIALS";
val warmup = setting "LIST_NOT_NIL_WARMUP";

val _ = load "listTheory";
val _ = load "metisLib";
val _ = Feedback.set_trace "metis" 0;

val goal = Parse.Term [Portable.QUOTE "!ls. ls <> [] <=> (ls = HD ls::TL ls)"];
val premises = [listTheory.list_CASES, listTheory.HD, listTheory.TL,
                listTheory.NOT_NIL_CONS];

fun prove_one () = Tactical.prove (goal, metisLib.METIS_TAC premises);

fun check theorem =
  if null (Thm.hyp theorem) andalso
     Term.aconv (Thm.concl theorem) (Thm.concl listTheory.LIST_NOT_NIL)
  then () else raise Fail "LIST_NOT_NIL proof mismatch";

val _ = let
  val _ = Count.reset_thm_count ()
  val _ = Count.counting_thms true
  val theorem = prove_one ()
  val _ = Count.counting_thms false
  val _ = check theorem
  val total = #total (Count.thm_count ())
in
  print ("LIST_NOT_NIL_INFERENCES\thol4\t" ^ Int.toString total ^ "\n")
end;

fun repeat 0 (SOME theorem) = theorem
  | repeat 0 NONE = raise Fail "zero proof iterations"
  | repeat remaining _ = repeat (remaining - 1) (SOME (prove_one ()));

val _ = check (repeat warmup NONE);

fun run_trial trial = let
  val _ = PolyML.fullGC ()
  val start = Time.now ()
  val theorem = repeat iterations NONE
  val elapsed = Time.toNanoseconds (Time.- (Time.now (), start))
  val _ = check theorem
  val _ = print (marker ^ "\thol4\t" ^ Int.toString trial ^ "\t" ^
                 Int.toString iterations ^ "\t" ^ LargeInt.toString elapsed ^ "\n")
in
  ()
end;

val _ = List.app run_trial (List.tabulate (trials, fn i => i));
