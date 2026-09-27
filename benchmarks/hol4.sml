val batch = 256;
val marker = "HOTARU_BENCH";

fun setting name =
  let val value = valOf (Int.fromString (valOf (OS.Process.getEnv name)))
  in if value > 0 then value else raise Fail ("invalid " ^ name) end;

fun parse_case row =
  case String.tokens (fn c => c = #":") row of
    [kind, parameter, iterations] =>
      let val parameter = valOf (Int.fromString parameter)
          val iterations = valOf (Int.fromString iterations)
      in
        if iterations > 0 andalso iterations mod batch = 0
        then (kind, parameter, iterations)
        else raise Fail ("invalid benchmark case: " ^ row)
      end
  | _ => raise Fail ("invalid benchmark case: " ^ row);

val cases = map parse_case
  (String.tokens (fn c => c = #";")
    (valOf (OS.Process.getEnv "HOTARU_BENCH_SPEC")));
val trials = setting "HOTARU_BENCH_TRIALS";
val warmup = setting "HOTARU_BENCH_WARMUP";
val _ = if warmup mod batch = 0 then () else raise Fail "invalid warmup";

val b = Type.bool;
val p = Term.mk_var ("p", b);
val f = Term.mk_var ("f", Type.mk_type ("fun", [b, b]));

fun build 0 term = term
  | build depth term = build (depth - 1) (Term.mk_comb (f, term));

fun sample iterations retain make =
  if retain then let
    val start = Time.now ()
    val results = Array.tabulate (iterations, fn _ => make ())
    val elapsed_ns = Time.toNanoseconds (Time.- (Time.now (), start))
  in
    (elapsed_ns, Array.sub (results, iterations - 1))
  end else let
    fun batches 0 last = last
      | batches remaining last = let
          val block = Array.tabulate (batch, fn _ => make ())
        in
          batches (remaining - 1) (SOME (Array.sub (block, batch - 1)))
        end
    val start = Time.now ()
    val last = batches (iterations div batch) NONE
    val elapsed_ns = Time.toNanoseconds (Time.- (Time.now (), start))
  in
    (elapsed_ns, valOf last)
  end;

fun check theorem expected assumptions =
  if Term.aconv (Thm.concl theorem) expected andalso
     List.length (Thm.hyp theorem) = assumptions
  then () else raise Fail "unexpected theorem";

fun measure kind parameter iterations expected assumptions make = let
  val retain = kind = "refl_retain"
  val (_, warm) = sample warmup retain make
  val _ = check warm expected assumptions
  fun trial i = if i = trials then () else let
    val _ = PolyML.fullGC ()
    val (elapsed_ns, theorem) = sample iterations retain make
    val _ = check theorem expected assumptions
    val _ = print (marker ^ "\t" ^ kind ^ "\t" ^ Int.toString parameter ^
      "\t" ^ Int.toString i ^ "\t" ^ Int.toString iterations ^ "\t" ^
      LargeInt.toString elapsed_ns ^ "\n")
  in
    trial (i + 1)
  end
in
  trial 0
end;

fun eq_term left right = boolSyntax.mk_eq (left, right);

fun equality_chain vars first last =
  if first = last then Thm.REFL (Array.sub (vars, first))
  else let
    val initial = Thm.ASSUME
      (eq_term (Array.sub (vars, first)) (Array.sub (vars, first + 1)))
    fun extend i chain =
      if i = last then chain
      else extend (i + 1) (Thm.TRANS chain
        (Thm.ASSUME
          (eq_term (Array.sub (vars, i)) (Array.sub (vars, i + 1)))))
  in
    extend (first + 1) initial
  end;

fun run_case (kind, parameter, iterations) =
  case kind of
    "refl_reuse" => let
      val term = build parameter p
      val expected = Thm.concl (Thm.REFL term)
    in
      measure kind parameter iterations expected 0 (fn () => Thm.REFL term)
    end
  | "refl_checked" => let
      val term = build parameter p
      val expected = Thm.concl (Thm.REFL term)
    in
      measure kind parameter iterations expected 0 (fn () => Thm.REFL term)
    end
  | "refl_retain" => let
      val term = build parameter p
      val expected = Thm.concl (Thm.REFL term)
    in
      measure kind parameter iterations expected 0 (fn () => Thm.REFL term)
    end
  | "refl_build" => let
      val term = build parameter p
      val expected = Thm.concl (Thm.REFL term)
    in
      measure kind parameter iterations expected 0
        (fn () => Thm.REFL (build parameter p))
    end
  | "assume" =>
      measure kind parameter iterations p 1 (fn () => Thm.ASSUME p)
  | "eq_mp" => let
      val equality = Thm.REFL p
      val premise = Thm.ASSUME p
    in
      measure kind parameter iterations p 1
        (fn () => Thm.EQ_MP equality premise)
    end
  | "trans_hyps" => let
      val count = parameter
      val vars = Array.tabulate (2 * count + 1,
        fn i => Term.mk_var ("x" ^ Int.toString i, b))
      val left = equality_chain vars 0 count
      val right = equality_chain vars count (2 * count)
      val expected = eq_term (Array.sub (vars, 0)) (Array.sub (vars, 2 * count))
    in
      measure kind parameter iterations expected (2 * count)
        (fn () => Thm.TRANS left right)
    end
  | "trace" => let
      val fp = Term.mk_comb (f, p)
      fun prove () = let
        val tf = Thm.REFL f
        val tp = Thm.REFL p
        val app = Thm.MK_COMB (tf, tp)
        val chain = Thm.TRANS app app
        val premise = Thm.ASSUME fp
      in
        Thm.EQ_MP chain premise
      end
    in
      measure kind parameter iterations fp 1 prove
    end
  | _ => raise Fail ("unknown benchmark case: " ^ kind);

val _ = List.app run_case cases;
