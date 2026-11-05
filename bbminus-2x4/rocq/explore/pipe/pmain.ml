open Pipe_out
let sym = function Coq__UU03a3_0 -> "0" | Coq__UU03a3_1 -> "1" | Coq__UU03a3_2 -> "2" | Coq__UU03a3_3 -> "3"
let tr = function None -> "---" | Some t -> sym t.out ^ (match t.dir0 with Dneg -> "L" | Dpos -> "R") ^ (match t.nxt with St0 -> "A" | St1 -> "B")
let tmstr tm =
  let ((((((((a0,a1),a2),a3),b0),b1),b2),b3)) = unmakeTM tm in
  String.concat "" [tr a0;tr a1;tr a2;tr a3;"_";tr b0;tr b1;tr b2;tr b3]
let mkdec s : haltDecider =
  match String.split_on_char ':' s with
  | ["loop"; n] -> loop1_decider (int_of_string n)
  | ["ng2"; a; b; g] -> nGramCPS_decider_impl2 (int_of_string a) (int_of_string b) (int_of_string g)
  | ["ng1"; h; a; b; g] -> nGramCPS_decider_impl1 (int_of_string h) (int_of_string a) (int_of_string b) (int_of_string g)
  | ["lru"; a; b; g] -> nGramCPS_LRU_decider (int_of_string a) (int_of_string b) (int_of_string g)
  | ["rwl"; l; m; t; n] -> repWL_ES_decider (int_of_string l) (int_of_string m) (int_of_string t) (int_of_string n)
  | ["halt"; n] -> halt_decider (int_of_string n)
  | _ -> failwith ("bad decider " ^ s)
let () =
  let specs = String.split_on_char ',' Sys.argv.(3) in
  let decs = List.mapi (fun i s -> (Obj.magic (mkdec s), (Obj.magic (i+1) : deciderIdentifier))) specs in
  let f = haltDecider_list decs in
  (* path: "-1" = root, "k" = child k, "k.j" = grandchild j of child k *)
  let path = List.map int_of_string (String.split_on_char '.' Sys.argv.(2)) in
  let start = match path with
    | [-1] -> [root]
    | k :: rest ->
      let rec descend node = function
        | [] -> [node]
        | j :: tl ->
          (match fst (f (tNF_tm node)) with
           | Result_Halt (s, i) -> descend (List.nth (tNF_Node_expand node s i) j) tl
           | _ -> failwith "not expandable") in
      descend (List.nth children k) rest
    | [] -> failwith "path" in
  let t0 = Unix.gettimeofday () in
  let rec loop q = match q with ([], q2) -> q2 | _ -> loop (searchQueue_upds q f 14) in
  let unk = loop (start, []) in
  let oc = open_out Sys.argv.(1) in
  List.iter (fun n -> output_string oc (tmstr (tNF_tm n) ^ "\n")) unk;
  close_out oc;
  Printf.printf "path %s total decided %d, undecided %d, time %.1fs\n" Sys.argv.(2) !Stats.total (List.length unk) (Unix.gettimeofday () -. t0);
  List.iteri (fun i s -> Printf.printf "  %-24s halt %9d nonhalt %9d\n" s Stats.nh.(i+1) Stats.nn.(i+1)) specs
