(* Driver: checks orbit segments with the extracted checker and prints exact results.
   check SEG  : Z B Z1 Y on argv: the reset state (a0=Z,B) must reach (a0=Z1,Y).
   final      : Z B on argv: from (a0=Z,B) to the halt form.
   Numbers on the command line are decimal; results are decimal too. This file only reads and prints. *)
open Checker

let w_of_decimal s =
  let r = ref (wc (Uint63.of_int 0)) in
  String.iter (fun c ->
    r := add1 (mulk (Uint63.of_int 10) !r) (wc (Uint63.of_int (Char.code c - 48)))) s;
  !r

let vl v = [v.v0; v.v1; v.v2; v.v3; v.v4]

(* decimal printing of little-endian 63-bit limbs, by repeated short division *)
let dec_of_limbs l =
  let limbs = Array.of_list (List.rev l) in
  let digits = Buffer.create 100 in
  let nz () = Array.exists (fun x -> not (Uint63.equal x (Uint63.of_int 0))) limbs in
  let base = Uint63.of_int 1000000000000000000 in
  let chunks = ref [] in
  while nz () do
    let r = ref (Uint63.of_int 0) in
    Array.iteri (fun i x ->
      let (q, r') = Uint63.div21 !r x base in
      limbs.(i) <- q; r := r') limbs;
    chunks := !r :: !chunks
  done;
  (match !chunks with
   | [] -> Buffer.add_string digits "0"
   | h :: t ->
     Buffer.add_string digits (Int64.to_string (Uint63.to_int64 h));
     List.iter (fun c -> Buffer.add_string digits (Printf.sprintf "%018Ld" (Uint63.to_int64 c))) t);
  Buffer.contents digits

let dec_of_w (x : w) = dec_of_limbs [x.lo; x.hi]
let z_of s = match s with "6" -> false | "22" -> true | _ -> failwith "reset value must be 6 or 22"

let () =
  let t0 = Unix.gettimeofday () in
  (match Sys.argv.(1) with
   | "seg" ->
     let z = z_of Sys.argv.(2) and b = w_of_decimal Sys.argv.(3)
     and z1 = z_of Sys.argv.(4) and y = w_of_decimal Sys.argv.(5) in
     (match check_seg z b z1 y with
      | Some (n, acc) -> Printf.printf "OK seg %s %s %s %s apps %s acc %s" Sys.argv.(2) Sys.argv.(3) Sys.argv.(4) Sys.argv.(5) (dec_of_w n) (dec_of_limbs (vl acc))
      | None -> Printf.printf "FAIL seg %s %s %s %s" Sys.argv.(2) Sys.argv.(3) Sys.argv.(4) Sys.argv.(5))
   | "final" ->
     let z = z_of Sys.argv.(2) and b = w_of_decimal Sys.argv.(3) in
     (match check_final z b with
      | Some ((a, n), acc) -> Printf.printf "OK final %s %s a %s apps %s acc %s" Sys.argv.(2) Sys.argv.(3) (dec_of_w a) (dec_of_w n) (dec_of_limbs (vl acc))
      | None -> Printf.printf "FAIL final %s %s" Sys.argv.(2) Sys.argv.(3))
   | "chunks" ->
     (* chunks FILE N K DONEFILE: for every line "id seg z B z1 Y" of FILE with id mod N = K and id not in DONEFILE,
        run check_seg and append "id seg OK apps acc phases-free secs" to stdout. Lines are independent; rerun to resume. *)
     let file = Sys.argv.(2) and n = int_of_string Sys.argv.(3) and k = int_of_string Sys.argv.(4) in
     let done_ = Hashtbl.create 1000 in
     (if Array.length Sys.argv > 5 && Sys.file_exists Sys.argv.(5) then begin
        let ic = open_in Sys.argv.(5) in
        (try while true do
           let l = input_line ic in
           (match String.split_on_char ' ' l with id :: _ -> Hashtbl.replace done_ id () | [] -> ())
         done with End_of_file -> close_in ic) end);
     let ic = open_in file in
     (try while true do
        let l = input_line ic in
        (match String.split_on_char ' ' l with
         | [id; seg; z; b; "H"; _] when (int_of_string id) mod n = k && not (Hashtbl.mem done_ id) ->
           let t1 = Unix.gettimeofday () in
           (match check_final (z_of z) (w_of_decimal b) with
            | Some ((a, nn), acc) ->
              Printf.printf "%s %s HALT %s %s %s %.2f\n%!" id seg (dec_of_w a) (dec_of_w nn) (dec_of_limbs (vl acc)) (Unix.gettimeofday () -. t1)
            | None -> Printf.printf "%s %s FAIL\n%!" id seg)
         | [id; seg; z; b; z1; y] when (int_of_string id) mod n = k && not (Hashtbl.mem done_ id) ->
           let t1 = Unix.gettimeofday () in
           (match check_seg (z_of z) (w_of_decimal b) (z_of z1) (w_of_decimal y) with
            | Some (nn, acc) ->
              Printf.printf "%s %s OK %s %s %.2f\n%!" id seg (dec_of_w nn) (dec_of_limbs (vl acc)) (Unix.gettimeofday () -. t1)
            | None -> Printf.printf "%s %s FAIL\n%!" id seg)
         | _ -> ())
      done with End_of_file -> close_in ic)
   | _ -> failwith "usage: check seg Z B Z1 Y | final Z B | chunks FILE N K [DONE]");
  Printf.printf " secs %.3f\n" (Unix.gettimeofday () -. t0)
