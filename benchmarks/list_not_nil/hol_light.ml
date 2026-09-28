open Hol_lib

let marker = "LIST_NOT_NIL_BENCH"

let setting name default =
  let value =
    match Sys.getenv_opt name with
    | Some raw -> int_of_string raw
    | None -> default
  in
  if value <= 0 then failwith ("invalid " ^ name);
  value

let iterations = setting "LIST_NOT_NIL_ITERATIONS" 8
let trials = setting "LIST_NOT_NIL_TRIALS" 7
let warmup = setting "LIST_NOT_NIL_WARMUP" 1

let target = `!ls:(A)list. ~(ls = []) <=> (ls = CONS (HD ls) (TL ls))`

let prove_target () =
  Sys.opaque_identity (prove (target,
    GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `ls:(A)list` list_CASES) THEN
    ASM_REWRITE_TAC [HD; TL; NOT_CONS_NIL] THEN
    MESON_TAC [NOT_CONS_NIL]))

let check theorem =
  if not (aconv (concl theorem) target) || hyp theorem <> [] then
    failwith "unexpected LIST_NOT_NIL theorem"

let sample count =
  let last = ref None in
  let start = Unix.gettimeofday () in
  for _ = 1 to count do
    last := Some (prove_target ())
  done;
  let elapsed_ns = Int64.of_float ((Unix.gettimeofday () -. start) *. 1e9) in
  match !last with
  | Some theorem -> elapsed_ns, theorem
  | None -> failwith "empty benchmark"

let () =
  let _, theorem = sample warmup in
  check theorem;
  for trial = 0 to trials - 1 do
    Gc.full_major ();
    let elapsed_ns, theorem = sample iterations in
    check theorem;
    Printf.printf "%s\thol-light\t%d\t%d\t%Ld\n%!"
      marker trial iterations elapsed_ns
  done
