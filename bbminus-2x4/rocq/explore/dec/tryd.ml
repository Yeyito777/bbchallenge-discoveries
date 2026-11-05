open Decx
let sym c = match c with '0' -> Coq__UU03a3_0 | '1' -> Coq__UU03a3_1 | '2' -> Coq__UU03a3_2 | _ -> Coq__UU03a3_3
let symi = function Coq__UU03a3_0 -> 0 | Coq__UU03a3_1 -> 1 | Coq__UU03a3_2 -> 2 | Coq__UU03a3_3 -> 3
let parse s =
  let s = String.concat "" (String.split_on_char '_' s) in
  let tbl = Array.init 8 (fun i ->
    let c = String.sub s (3*i) 3 in
    if c.[0] = '-' then None else
    Some { nxt = (if c.[2] = 'A' then St0 else St1); dir0 = (if c.[1] = 'R' then Dpos else Dneg); out = sym c.[0] }) in
  fun st i -> tbl.((match st with St0 -> 0 | St1 -> 4) + symi i)
let () =
  let a = Sys.argv in
  let ia k = int_of_string a.(k) in
  let dec : _UU03a3_ tM -> haltDecideResult = match a.(1) with
    | "loop" -> loop1_decider (ia 2)
    | "ng2" -> nGramCPS_decider_impl2 (ia 2) (ia 3) (ia 4)
    | "ng1" -> nGramCPS_decider_impl1 (ia 2) (ia 3) (ia 4) (ia 5)
    | "lru" -> nGramCPS_LRU_decider (ia 2) (ia 3) (ia 4)
    | "rwl" -> repWL_ES_decider (ia 2) (ia 3) (ia 4) (ia 5)
    | "halt" -> halt_decider (ia 2)
    | _ -> failwith "decider" in
  let nh = ref 0 and nn = ref 0 and nu = ref 0 in
  let t0 = Unix.gettimeofday () in
  (try while true do
    let l = String.trim (input_line stdin) in
    if l <> "" then
    match dec (parse l) with
    | Result_Halt _ -> incr nh; Printf.eprintf "HALT %s\n%!" l
    | Result_NonHalt -> incr nn
    | Result_Unknown -> incr nu; print_endline l
  done with End_of_file -> ());
  Printf.eprintf "%s: halt %d nonhalt %d unknown %d (%.1fs)\n%!" (String.concat " " (Array.to_list (Array.sub a 1 (Array.length a - 1)))) !nh !nn !nu (Unix.gettimeofday () -. t0)
