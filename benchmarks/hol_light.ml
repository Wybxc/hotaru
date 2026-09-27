open Hol_lib

let batch = 256
let marker = "HOTARU_BENCH"

let setting name =
  let value = int_of_string (Sys.getenv name) in
  if value <= 0 then failwith ("invalid " ^ name);
  value

let parse_case row =
  match String.split_on_char ':' row with
  | [kind; parameter; iterations] ->
      let parameter = int_of_string parameter
      and iterations = int_of_string iterations in
      if iterations <= 0 || iterations mod batch <> 0 then
        failwith ("invalid benchmark case: " ^ row);
      kind, parameter, iterations
  | _ -> failwith ("invalid benchmark case: " ^ row)

let cases =
  String.split_on_char ';' (Sys.getenv "HOTARU_BENCH_SPEC")
  |> List.map parse_case

let trials = setting "HOTARU_BENCH_TRIALS"
let warmup = setting "HOTARU_BENCH_WARMUP"
let () = if warmup mod batch <> 0 then failwith "invalid warmup"

let b = bool_ty
let p = mk_var ("p", b)
let f = mk_var ("f", mk_fun_ty b b)

let rec build depth term =
  if depth = 0 then term else build (depth - 1) (mk_comb (f, term))

let sample iterations retain make =
  if retain then begin
    let start = Unix.gettimeofday () in
    let results = Sys.opaque_identity (Array.init iterations (fun _ -> make ())) in
    let elapsed_ns = Int64.of_float ((Unix.gettimeofday () -. start) *. 1e9) in
    elapsed_ns, results.(iterations - 1)
  end else begin
    let last = ref None in
    let start = Unix.gettimeofday () in
    for _ = 1 to iterations / batch do
      let block = Sys.opaque_identity (Array.init batch (fun _ -> make ())) in
      last := Some block.(batch - 1)
    done;
    let elapsed_ns = Int64.of_float ((Unix.gettimeofday () -. start) *. 1e9) in
    match !last with
    | Some theorem -> elapsed_ns, theorem
    | None -> failwith "empty benchmark"
  end

let check theorem expected assumptions =
  if concl theorem <> expected || List.length (hyp theorem) <> assumptions then
    failwith "unexpected theorem"

let measure kind parameter iterations expected assumptions make =
  let retain = kind = "refl_retain" in
  let _, theorem = sample warmup retain make in
  check theorem expected assumptions;
  for trial = 0 to trials - 1 do
    Gc.full_major ();
    let elapsed_ns, theorem = sample iterations retain make in
    check theorem expected assumptions;
    Printf.printf "%s\t%s\t%d\t%d\t%d\t%Ld\n%!"
      marker kind parameter trial iterations elapsed_ns
  done

let equality_chain vars first last =
  if first = last then REFL vars.(first)
  else begin
    let chain = ref (ASSUME (mk_eq (vars.(first), vars.(first + 1)))) in
    for i = first + 1 to last - 1 do
      chain := TRANS !chain (ASSUME (mk_eq (vars.(i), vars.(i + 1))))
    done;
    !chain
  end

let run_case (kind, parameter, iterations) =
  match kind with
  | "refl_reuse" | "refl_checked" | "refl_retain" ->
      let term = build parameter p in
      measure kind parameter iterations (mk_eq (term, term)) 0
        (fun () -> REFL (Sys.opaque_identity term))
  | "refl_build" ->
      let term = build parameter p in
      measure kind parameter iterations (mk_eq (term, term)) 0
        (fun () -> REFL (build parameter p))
  | "assume" ->
      measure kind parameter iterations p 1
        (fun () -> ASSUME (Sys.opaque_identity p))
  | "eq_mp" ->
      let equality = REFL p and premise = ASSUME p in
      measure kind parameter iterations p 1
        (fun () -> EQ_MP equality premise)
  | "trans_hyps" ->
      let count = parameter in
      let vars = Array.init (2 * count + 1)
        (fun i -> mk_var ("x" ^ string_of_int i, b)) in
      let left = equality_chain vars 0 count
      and right = equality_chain vars count (2 * count) in
      measure kind parameter iterations (mk_eq (vars.(0), vars.(2 * count)))
        (2 * count) (fun () -> TRANS left right)
  | "trace" ->
      let fp = mk_comb (f, p) in
      measure kind parameter iterations fp 1 (fun () ->
        let tf = REFL f in
        let tp = REFL p in
        let app = MK_COMB (tf, tp) in
        let chain = TRANS app app in
        let premise = ASSUME fp in
        EQ_MP chain premise)
  | _ -> failwith ("unknown benchmark case: " ^ kind)

let () = List.iter run_case cases
