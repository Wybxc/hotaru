val article_path = valOf (OS.Process.getEnv "LIST_NOT_NIL_ARTICLE");

val _ = load "listTheory";
val _ = load "metisLib";
val _ = load "Logging";
val _ = Feedback.set_trace "metis" 0;

val _ = Logging.set_tyop_name_handler (fn {Thy, Tyop} =>
  case (Thy, Tyop) of
    ("min", "fun") => ([], "->")
  | ("min", "bool") => ([], "bool")
  | _ => (["HOL4", Thy], Tyop));

val _ = Logging.set_const_name_handler (fn {Thy, Name} =>
  case (Thy, Name) of
    ("min", "=") => ([], "=")
  | ("arithmetic", "NUMERAL") => (["Unwanted"], "id")
  | _ => (["HOL4", Thy], Name));

val goal = Parse.Term [Portable.QUOTE "!ls. ls <> [] <=> (ls = HD ls::TL ls)"];
val premises = [listTheory.list_CASES, listTheory.HD, listTheory.TL,
                listTheory.NOT_NIL_CONS];

fun prove_one () = Tactical.prove (goal, metisLib.METIS_TAC premises);

fun check theorem =
  if null (Thm.hyp theorem) andalso
     Term.aconv (Thm.concl theorem) (Thm.concl listTheory.LIST_NOT_NIL)
  then () else raise Fail "LIST_NOT_NIL proof mismatch";

val _ = let
  val output = TextIO.openOut article_path
  val _ = Logging.raw_start_logging [] output
  val _ = Count.reset_thm_count ()
  val _ = Count.counting_thms true
  val theorem = prove_one ()
  val _ = Count.counting_thms false
  val _ = check theorem
  val total = #total (Count.thm_count ())
  val _ = ignore (Logging.export_thm theorem)
  val _ = Logging.stop_logging ()
in
  print ("LIST_NOT_NIL_INFERENCES\thol4-ot\t" ^ Int.toString total ^ "\n")
end;

val commands = ["axiom", "absThm", "appThm", "assume", "betaConv",
                "deductAntisym", "eqMp", "refl", "subst", "sym", "trans"];

val counts = map (fn command => (command, ref 0)) commands;

val _ = let
  val input = TextIO.openIn article_path
  fun read () =
    case TextIO.inputLine input of
      NONE => ()
    | SOME line =>
        (List.app (fn (command, count) =>
          if line = command ^ "\n" then count := !count + 1 else ()) counts;
         read ())
  val _ = read ()
  val _ = TextIO.closeIn input
  val _ = List.app (fn (command, count) =>
    if !count > 0 then
      print ("LIST_NOT_NIL_ARTICLE_COUNT\t" ^ command ^ "\t" ^
             Int.toString (!count) ^ "\n")
    else ()) counts
in
  ()
end;
