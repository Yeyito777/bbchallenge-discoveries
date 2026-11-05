open Explore_out
let sym = function Coq__UU03a3_0 -> "0" | Coq__UU03a3_1 -> "1" | Coq__UU03a3_2 -> "2" | Coq__UU03a3_3 -> "3"
let tr = function None -> "---" | Some t -> sym t.out ^ (match t.dir0 with Dneg -> "L" | Dpos -> "R") ^ (match t.nxt with St0 -> "A" | St1 -> "B")
let tmstr tm =
  let ((((((((a0,a1),a2),a3),b0),b1),b2),b3)) = unmakeTM tm in
  String.concat "" [tr a0;tr a1;tr a2;tr a3;"_";tr b0;tr b1;tr b2;tr b3]
let () =
  let t0 = Unix.gettimeofday () in
  let rec loop q = match q with ([], q2) -> q2 | _ -> loop (step_all q) in
  let k = int_of_string Sys.argv.(2) in
  let start = if k < 0 then root else List.nth children k in
  let unk = loop ([start],[]) in
  let oc = open_out Sys.argv.(1) in
  List.iter (fun n -> output_string oc (tmstr (tNF_tm n) ^ "\n")) unk;
  close_out oc;
  Printf.printf "total decided %d, undecided %d, time %.1fs\n" !Stats.total (List.length unk) (Unix.gettimeofday () -. t0);
  for i = 0 to 63 do
    if Stats.nh.(i) + Stats.nn.(i) > 0 then Printf.printf "decider %d: halt %d nonhalt %d\n" i Stats.nh.(i) Stats.nn.(i)
  done
