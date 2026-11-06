(** Extraction of the checker to OCaml, on primitive 63-bit ints. *)
From Coq Require Import Extraction ExtrOCamlInt63.
From BB6 Require Import Num Big Vec Walk Step Check.
Set Extraction Output Directory "extract".
Extraction Language OCaml.
(* The division in [bnd] and in the jump length is only ever a suggestion: bnd_spec and valid_take check the result by
   multiplying back, and no proof looks inside [adiv]. So in OCaml it is replaced by a float estimate, refined by the remainder. *)
Extract Constant adiv =>
 "(fun g m ->
    let open Uint63 in
    let two63 = 9223372036854775808.0 in
    let fl x = let f = Stdlib.float_of_int (x land Stdlib.max_int) in if x < 0 then f +. 4611686018427387904.0 else f in
    let flw w = fl (Obj.magic w.hi) *. two63 +. fl (Obj.magic w.lo) in
    let mf = flw m in
    let wf q =
      if q < 4.0e18 then { hi = of_int 0; lo = of_int (Stdlib.int_of_float q) }
      else
        let h = Float.of_int (Stdlib.int_of_float (q /. two63)) in
        { hi = of_int (Stdlib.int_of_float h); lo = of_int (Stdlib.int_of_float (Float.min 4.0e18 (q -. h *. two63))) } in
    let wsub a b = { hi = sub (sub a.hi b.hi) (if lt a.lo b.lo then of_int 1 else of_int 0); lo = sub a.lo b.lo } in
    let wadd a b = let l = add a.lo b.lo in { hi = add (add a.hi b.hi) (if lt l a.lo then of_int 1 else of_int 0); lo = l } in
    let q1 = flw g /. mf in
    if q1 < 1.0e11 then { hi = of_int 0; lo = of_int (Stdlib.int_of_float (q1 *. 0.9999999999999)) }
    else
    let rec go g acc n =
      let q = flw g /. mf *. 0.99999999999 in
      if q < 1.0 || n = 0 then acc else
      let qw = wf q in
      (match mul_nn m qw with
       | Some p -> go (wsub g p) (wadd acc qw) (n - 1)
       | None -> acc) in
    go g { hi = of_int 0; lo = of_int 0 } 6)".
Extraction Inline add sub ltb leb eqb fits is_neg adc flip wc neg low2 odd4 b2i.
Extraction "checker.ml" check_seg check_final mulk add wc.
