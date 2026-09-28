open Hol_lib

type value =
    Name of string
  | Number of int
  | Tyop of string
  | Ty of hol_type
  | Const of string
  | Var of term
  | Tm of term
  | Theorem of thm
  | Values of value list

type instruction = Push of value | Command of string

let setting name =
  let value = int_of_string (Sys.getenv name) in
  if value <= 0 then failwith ("invalid " ^ name);
  value

let iterations = setting "LIST_NOT_NIL_ITERATIONS"
let trials = setting "LIST_NOT_NIL_TRIALS"
let warmup = setting "LIST_NOT_NIL_WARMUP"

let decode_name line =
  let n = String.length line in
  if n < 2 || line.[n - 1] <> '"' then failwith "bad article name";
  let buffer = Buffer.create (n - 2) in
  let rec read i =
    if i >= n - 1 then Buffer.contents buffer
    else if line.[i] = '\\' then begin
      if i + 1 >= n - 1 then failwith "bad article name escape";
      Buffer.add_char buffer line.[i + 1];
      read (i + 2)
    end else begin
      Buffer.add_char buffer line.[i];
      read (i + 1)
    end
  in
  read 1

let parse_line line =
  let line = String.trim line in
  if line = "" || line.[0] = '#' then None
  else if line.[0] = '"' then Some (Push (Name (decode_name line)))
  else if line.[0] >= '0' && line.[0] <= '9' then
    Some (Push (Number (int_of_string line)))
  else Some (Command line)

let read_article path =
  let channel = open_in path in
  let rec read acc =
    match input_line channel with
    | line ->
        let acc = match parse_line line with Some op -> op :: acc | None -> acc in
        read acc
    | exception End_of_file ->
        close_in channel;
        Array.of_list (List.rev acc)
  in
  try read [] with error -> close_in_noerr channel; raise error

let type_op = function
  | "bool" | "Data.Bool.bool" -> "bool"
  | "fun" | "->" | "Function.fun" -> "fun"
  | "ind" | "HOL4.min.ind" -> "ind"
  | "Data.List.list" | "HOL4.list.list" -> "list"
  | name -> failwith ("unmapped OpenTheory type operator: " ^ name)

let constant = function
  | "=" | "HOL4.min.=" -> "="
  | "select" | "HOL4.min.@" -> "@"
  | "Data.Bool.!" | "HOL4.bool.!" -> "!"
  | "Data.Bool.?" | "HOL4.bool.?" -> "?"
  | "Data.Bool.?!" | "HOL4.bool.?!" -> "?!"
  | "Data.Bool.T" | "HOL4.bool.T" -> "T"
  | "Data.Bool.F" | "HOL4.bool.F" -> "F"
  | "Data.Bool./\\" | "HOL4.bool./\\" -> "/\\"
  | "Data.Bool.\\/" | "HOL4.bool.\\/" -> "\\/"
  | "Data.Bool.==>" | "HOL4.min.==>" -> "==>"
  | "Data.Bool.~" | "HOL4.bool.~" -> "~"
  | "Data.List.[]" | "HOL4.list.NIL" -> "NIL"
  | "Data.List.::" | "HOL4.list.CONS" -> "CONS"
  | "Data.List.head" | "HOL4.list.HD" -> "HD"
  | "Data.List.tail" | "HOL4.list.TL" -> "TL"
  | name -> failwith ("unmapped OpenTheory constant: " ^ name)

let nil_cons_reordered = prove
  (`!t (h:A). ~([] = CONS h t)`, MESON_TAC [NOT_CONS_NIL])
let hd_quantified = prove
  (`!(h:A) t. HD (CONS h t) = h`, REWRITE_TAC [HD])

let implication_antisym =
  ITAUT `!p q. (p ==> q) ==> (q ==> p) ==> (p <=> q)`

let double_negation = CONJUNCT1 NOT_CLAUSES

let contradiction = TAUT `(~p ==> F) ==> (p ==> F) ==> F`
let direct_contradiction = TAUT `!p. p ==> ~p ==> F`
let not_imp_left = TAUT `~(p ==> q) ==> p`
let not_imp_right = TAUT `~(p ==> q) ==> ~q`
let not_or_contradiction =
  TAUT `(~(p \/ q) ==> F) <=> (p ==> F) ==> ~q ==> F`
let double_negation_elim = TAUT `~ ~p ==> p`
let not_or_left = TAUT `~(p \/ q) ==> ~p`
let not_or_contradiction_left =
  TAUT `(~(~p \/ q) ==> F) <=> p ==> ~q ==> F`
let implication_cnf = TAUT
  `(p <=> q ==> r) <=>
   (p \/ q) /\ (p \/ ~r) /\ (~q \/ r \/ ~p)`
let equality_cnf = TAUT
  `(p <=> (q <=> r)) <=>
   (p \/ q \/ r) /\ (p \/ ~r \/ ~q) /\
   (q \/ ~r \/ ~p) /\ (r \/ ~q \/ ~p)`
let not_or_right = TAUT `~(p \/ q) ==> ~q`
let false_implies = TAUT `!p. F ==> p`

let seeds =
  [TRUTH; IMP_DEF; FORALL_DEF; AND_DEF; implication_antisym; NOT_DEF;
   EQ_CLAUSES; double_negation; contradiction; direct_contradiction;
   not_imp_left; IMP_CLAUSES; not_imp_right; not_or_contradiction;
   double_negation_elim; not_or_left; not_or_contradiction_left;
   implication_cnf; equality_cnf; not_or_right; EXISTS_THM; EXISTS_DEF;
   OR_DEF; SELECT_AX; list_CASES; GEN_ALL TL; hd_quantified; EQ_REFL;
   false_implies; BOOL_CASES_AX; nil_cons_reordered]

let same_hypotheses left right =
  List.length left = List.length right &&
  List.for_all (fun h -> List.exists (aconv h) right) left

let resolve_axiom hypotheses conclusion =
  let rec search = function
    | [] -> failwith ("unmatched article axiom: " ^ string_of_term conclusion)
    | seed :: rest ->
        let candidate =
          try Some (INSTANTIATE (term_match [] (concl seed) conclusion) seed)
          with Failure _ -> None
        in
        (match candidate with
        | Some theorem when aconv (concl theorem) conclusion &&
                            same_hypotheses (hyp theorem) hypotheses -> theorem
        | _ -> search rest)
  in
  search seeds

let types command values =
  List.map (function Ty ty -> ty | _ -> failwith (command ^ ": expected types")) values

let terms command values =
  List.map (function Tm tm -> tm | _ -> failwith (command ^ ": expected terms")) values

let subst_pairs values =
  match values with
  | [Values type_pairs; Values term_pairs] ->
      let ty_subst = List.map (function
        | Values [Name name; Ty ty] -> ty, mk_vartype name
        | _ -> failwith "subst: invalid type pair") type_pairs in
      let tm_subst = List.map (function
        | Values [Var variable; Tm replacement] -> replacement, variable
        | _ -> failwith "subst: invalid term pair") term_pairs in
      ty_subst, tm_subst
  | _ -> failwith "subst: invalid substitutions"

let replay article =
  let stack = ref [] in
  let dictionary = Hashtbl.create 4096 in
  let outputs = ref [] in
  let push value = stack := value :: !stack in
  let execute = function
    | Push value -> push value
    | Command command ->
        match command, !stack with
        | "version", Number 6 :: rest -> stack := rest
        | "version", _ -> failwith "unsupported article version"
        | "nil", _ -> push (Values [])
        | "cons", Values tail :: head :: rest -> stack := Values (head :: tail) :: rest
        | "def", Number key :: value :: rest ->
            Hashtbl.replace dictionary key value;
            stack := value :: rest
        | "ref", Number key :: rest ->
            stack := Hashtbl.find dictionary key :: rest
        | "remove", Number key :: rest ->
            let value = Hashtbl.find dictionary key in
            Hashtbl.remove dictionary key;
            stack := value :: rest
        | "pop", _ :: rest -> stack := rest
        | "typeOp", Name name :: rest -> stack := Tyop (type_op name) :: rest
        | "varType", Name name :: rest -> stack := Ty (mk_vartype name) :: rest
        | "opType", Values arguments :: Tyop name :: rest ->
            stack := Ty (mk_type (name, types command arguments)) :: rest
        | "const", Name name :: rest -> stack := Const (constant name) :: rest
        | "constTerm", Ty ty :: Const name :: rest ->
            stack := Tm (mk_mconst (name, ty)) :: rest
        | "var", Ty ty :: Name name :: rest ->
            stack := Var (mk_var (name, ty)) :: rest
        | "varTerm", Var variable :: rest -> stack := Tm variable :: rest
        | "absTerm", Tm body :: Var variable :: rest ->
            stack := Tm (mk_abs (variable, body)) :: rest
        | "appTerm", Tm argument :: Tm function_ :: rest ->
            stack := Tm (mk_comb (function_, argument)) :: rest
        | "absThm", Theorem theorem :: Var variable :: rest ->
            stack := Theorem (ABS variable theorem) :: rest
        | "appThm", Theorem argument :: Theorem function_ :: rest ->
            stack := Theorem (MK_COMB (function_, argument)) :: rest
        | "assume", Tm term :: rest -> stack := Theorem (ASSUME term) :: rest
        | "axiom", Tm conclusion :: Values hypotheses :: rest ->
            stack := Theorem (resolve_axiom (terms command hypotheses) conclusion) :: rest
        | "betaConv", Tm term :: rest ->
            stack := Theorem (BETA_CONV term) :: rest
        | "deductAntisym", Theorem left :: Theorem right :: rest ->
            stack := Theorem (DEDUCT_ANTISYM_RULE right left) :: rest
        | "eqMp", Theorem premise :: Theorem equality :: rest ->
            stack := Theorem (try EQ_MP equality premise with Failure _ ->
              failwith ("eqMp: equality " ^ string_of_term (concl equality) ^
                        "; premise " ^ string_of_term (concl premise))) :: rest
        | "refl", Tm term :: rest -> stack := Theorem (REFL term) :: rest
        | "subst", Theorem theorem :: Values replacements :: rest ->
            let ty_subst, tm_subst = subst_pairs replacements in
            stack := Theorem (INST tm_subst (INST_TYPE ty_subst theorem)) :: rest
        | "sym", Theorem theorem :: rest -> stack := Theorem (SYM theorem) :: rest
        | "trans", Theorem right :: Theorem left :: rest ->
            stack := Theorem (TRANS left right) :: rest
        | "thm", Tm conclusion :: Values hypotheses :: Theorem theorem :: rest ->
            let hypotheses = terms command hypotheses in
            let theorem = List.fold_left (fun theorem hypothesis ->
              if List.exists (aconv hypothesis) (hyp theorem) then theorem
              else ADD_ASSUM hypothesis theorem) theorem hypotheses in
            if not (aconv (concl theorem) conclusion) ||
               not (same_hypotheses (hyp theorem) hypotheses) then
              failwith "thm: exported theorem does not match replay";
            outputs := theorem :: !outputs;
            stack := rest
        | "defineConst", _ | "defineTypeOp", _ ->
            failwith (command ^ ": definitions require an explicit library mapping")
        | _ -> failwith (command ^ ": invalid stack or unsupported command")
  in
  Array.iteri (fun index instruction ->
    try execute instruction with error ->
      failwith (Printf.sprintf "article instruction %d: %s"
        (index + 1) (Printexc.to_string error))) article;
  match !outputs with
  | [theorem] -> theorem
  | [] -> failwith "article exports no theorem"
  | _ -> failwith "article exports multiple theorems"

let target = `!ls:(A)list. ~(ls = []) <=> (ls = CONS (HD ls) (TL ls))`

let check theorem =
  let matches =
    try
      let _, _, ty_subst = term_match [] target (concl theorem) in
      aconv (inst ty_subst target) (concl theorem)
    with Failure _ -> false
  in
  if not matches || hyp theorem <> [] then
    failwith ("article did not prove LIST_NOT_NIL: " ^ string_of_thm theorem)

let sample path count =
  let last = ref None in
  let start = Unix.gettimeofday () in
  for _ = 1 to count do
    last := Some (replay (read_article path))
  done;
  let elapsed_ns = Int64.of_float ((Unix.gettimeofday () -. start) *. 1e9) in
  match !last with
  | Some theorem -> elapsed_ns, theorem
  | None -> failwith "empty benchmark"

let () =
  if Array.length Sys.argv <> 2 then failwith "usage: hol_light_replay ARTICLE";
  let path = Sys.argv.(1) in
  let _, theorem = sample path warmup in
  check theorem;
  for trial = 0 to trials - 1 do
    Gc.full_major ();
    let elapsed_ns, theorem = sample path iterations in
    check theorem;
    Printf.printf "LIST_NOT_NIL_REPLAY\thol-light\t%d\t%d\t%Ld\n%!"
      trial iterations elapsed_ns
  done
