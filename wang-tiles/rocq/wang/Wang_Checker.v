(** The certificate checker for "every n-tile set that tiles a DxD square tiles the plane".

    It walks the same tree as wang/code/check_cert.py (order "ringsym") and reads the same
    certificate tokens, including closed claims, the visit gate, and subtree resets shared out
    over shards. Everything the soundness proof relies on is computed here on plain inductive
    data (labels, relations as boolean matrices). Primitive integers and arrays are used only
    for the certificate stream, the torus table and three caches; no proof depends on what
    they contain: every claim is re-checked against the relations at the node where it is used,
    closed relations are kept in a separate structure and compared structurally, and every
    repeat-skip key is decoded and compared structurally. *)

From Coq Require Import List Arith Lia Bool PArith ZArith.
From Coq Require Import Uint63 PArray FMapPositive.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Rel Wang_Refute.

Module PM := PositiveMap.

Local Open Scope nat_scope.

(** ** Geometry of the DxD square and the fill order *)

Definition ring (lo hi : nat) : list (nat * nat) :=
  if Nat.eqb lo hi then [(lo, lo)] else
  map (fun c => (lo, c)) (seq lo (hi - lo)) ++
  map (fun r => (r, hi)) (seq lo (hi - lo)) ++
  map (fun c => (hi, hi + lo + 1 - c)) (seq (lo + 1) (hi - lo)) ++
  map (fun r => (hi + lo + 1 - r, lo)) (seq (lo + 1) (hi - lo)).

(** The ring order of wt_lazy: the centre first, then rings outwards. *)
Definition ring_cells (D : nat) : list (nat * nat) :=
  let lo0 := if Nat.odd D then D / 2 else D / 2 - 1 in
  let hi0 := D / 2 in
  flat_map (fun j => ring (lo0 - j) (hi0 + j)) (seq 0 (lo0 + 1)).

Definition cell (D p : nat) : nat * nat := nth p (ring_cells D) (0, 0).

Definition hadj (D p q : nat) : bool :=
  let '(r1, c1) := cell D p in let '(r2, c2) := cell D q in Nat.eqb r1 r2 && Nat.eqb (S c1) c2.
Definition vadj (D p q : nat) : bool :=
  let '(r1, c1) := cell D p in let '(r2, c2) := cell D q in Nat.eqb c1 c2 && Nat.eqb (S r1) r2.
Definition adj (D q r : nat) : bool := hadj D q r || hadj D r q || vadj D q r || vadj D r q.

Definition left_nb (D pos : nat) := filter (fun p => hadj D p pos) (seq 0 pos).
Definition right_nb (D pos : nat) := filter (fun q => hadj D pos q) (seq 0 pos).
Definition up_nb (D pos : nat) := filter (fun p => vadj D p pos) (seq 0 pos).
Definition down_nb (D pos : nat) := filter (fun q => vadj D pos q) (seq 0 pos).
(** The neighbours of cell (r, c) inside the DxD square. *)
Definition nbr_coords (D r c : nat) : list (nat * nat) :=
  (if Nat.ltb (S c) D then [(r, S c)] else []) ++ (if Nat.ltb 0 c then [(r, c - 1)] else []) ++
  (if Nat.ltb (S r) D then [(S r, c)] else []) ++ (if Nat.ltb 0 r then [(r - 1, c)] else []).

(** Computed versions that take the ring order [rc] once. *)
Definition hadj_of (rc : list (nat * nat)) (p q : nat) : bool :=
  let '(r1, c1) := nth p rc (0, 0) in let '(r2, c2) := nth q rc (0, 0) in Nat.eqb r1 r2 && Nat.eqb (S c1) c2.
Definition vadj_of (rc : list (nat * nat)) (p q : nat) : bool :=
  let '(r1, c1) := nth p rc (0, 0) in let '(r2, c2) := nth q rc (0, 0) in Nat.eqb c1 c2 && Nat.eqb (S r1) r2.

Definition pk (p : nat) : positive := Pos.of_succ_nat p.

(** The seven non-trivial symmetries of the square: optional transpose, then optional flips. *)
Definition symf (D : nat) (sw fr fc : bool) (x : nat * nat) : nat * nat :=
  let '(a, b) := if sw then (snd x, fst x) else x in
  (if fr then D - 1 - a else a, if fc then D - 1 - b else b).

Definition syms : list (bool * bool * bool) :=
  [(false, false, true); (false, true, false); (false, true, true); (true, false, false);
   (true, false, true); (true, true, false); (true, true, true)].

Definition pair_eqb (x y : nat * nat) : bool := Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Fixpoint index_of (x : nat * nat) (l : list (nat * nat)) (i : nat) : nat :=
  match l with [] => i | y :: l' => if pair_eqb x y then i else index_of x l' (S i) end.

Definition pos_of (D : nat) (x : nat * nat) : nat := index_of x (ring_cells D) 0.

(** The largest position of a neighbour of the cell at position q. *)
Definition maxnb_of (rc : list (nat * nat)) (D q : nat) : nat :=
  let '(r, c) := nth q rc (0, 0) in fold_left Nat.max (map (fun x => index_of x rc 0) (nbr_coords D r c)) 0.
Definition maxl_of (rc : list (nat * nat)) (D : nat) : list nat := map (maxnb_of rc D) (seq 0 (D * D)).

(** The frontier: placed cells with a neighbour not yet placed, in increasing order. *)
Definition frontier_of (ml : list nat) (pos : nat) : list nat := filter (fun q => Nat.leb pos (nth q ml 0)) (seq 0 pos).
Definition frontier (D pos : nat) : list nat := frontier_of (maxl_of (ring_cells D) D) pos.

(** [e_reset]: subtrees are reset at this position (P > 0 and pos = P); [e_pre] lists the cells
    0..P-1 there, whose labels are recorded. [e_deep]: no reset can happen between a node here
    and its parent's table lookup (no resets, or pos > P). *)
Record entry := mkE {
  e_key : positive; e_full : bool; e_reset : bool; e_deep : bool; e_pre : list positive;
  e_left : list positive; e_right : list positive; e_up : list positive; e_down : list positive;
  e_front : list positive }.

Definition is_reset (P pos : nat) : bool := negb (Nat.eqb P 0) && Nat.eqb pos P.

Definition mk_entry_of (rc : list (nat * nat)) (ml : list nat) (D P pos : nat) : entry :=
  mkE (pk pos) (Nat.eqb pos (D * D)) (is_reset P pos) (Nat.eqb P 0 || Nat.ltb P pos)
      (if is_reset P pos then map pk (seq 0 P) else [])
      (map pk (filter (fun p => hadj_of rc p pos) (seq 0 pos))) (map pk (filter (fun q => hadj_of rc pos q) (seq 0 pos)))
      (map pk (filter (fun p => vadj_of rc p pos) (seq 0 pos))) (map pk (filter (fun q => vadj_of rc pos q) (seq 0 pos)))
      (map pk (frontier_of ml pos)).

(** The entry of position pos: as [mk_entry_of], with [left_nb D pos] and so on. *)
Definition mk_entry (D P pos : nat) : entry := mk_entry_of (ring_cells D) (maxl_of (ring_cells D) D) D P pos.

Definition table (D P : nat) : list entry :=
  let rc := ring_cells D in let ml := maxl_of rc D in map (mk_entry_of rc ml D P) (seq 0 (S (D * D))).


Definition image (D : nat) (g : bool * bool * bool) : list nat :=
  let '(sw, fr, fc) := g in map (fun i => pos_of D (symf D sw fr fc (cell D i))) (seq 0 (D * D)).

Definition images (D : nat) : list (list positive) := map (fun g => map pk (image D g)) syms.

(** ** Labels of the cells placed so far *)

Definition lab (lm : PM.t nat) (q : positive) : nat :=
  match PM.find q lm with Some x => x | None => 0 end.

Fixpoint assoc_find (x : nat) (a : list (nat * nat)) : option nat :=
  match a with [] => None | (y, v) :: a' => if Nat.eqb x y then Some v else assoc_find x a' end.

(** One step of renaming labels by first appearance. *)
Definition rn_step (l : nat) (m : nat) (a : list (nat * nat)) : nat * nat * list (nat * nat) :=
  match assoc_find l a with Some y => (y, m, a) | None => (m, S m, (l, m) :: a) end.

(** Symmetric skip: the image under a symmetry, renamed by first appearance, reads smaller
    than the labels on the cells placed so far. *)
Fixpoint symloop (pkey : positive) (lm : PM.t nat) (img : list positive) (i : positive)
  (m : nat) (a : list (nat * nat)) : bool :=
  match img with
  | [] => false
  | q :: img' =>
    if Pos.ltb i pkey && Pos.ltb q pkey then
      let '(x, m', a') := rn_step (lab lm q) m a in
      let li := lab lm i in
      if Nat.ltb x li then true
      else if Nat.ltb li x then false
      else symloop pkey lm img' (Pos.succ i) m' a'
    else false
  end.

Definition sym_skip (imgs : list (list positive)) (pkey : positive) (lm : PM.t nat) : bool :=
  existsb (fun img => symloop pkey lm img 1 0 []) imgs.

(** ** Integers, used only for data, keys and caches *)

Local Open Scope uint63_scope.

Fixpoint int_of_nat (x : nat) : int := match x with O => 0 | S x' => int_of_nat x' + 1 end.
Definition nat_of_int (x : int) : nat := Z.to_nat (Uint63.to_Z x).
Fixpoint nat_of_small_aux (fuel : nat) (x : int) : nat :=
  match fuel with O => O | S f => if x =? 0 then O else S (nat_of_small_aux f (x - 1)) end.
Definition nat_of_small (x : int) : nat := nat_of_small_aux 64 x.
Fixpoint int_of_pos (p : positive) : int :=
  match p with xH => 1 | xO p' => int_of_pos p' << 1 | xI p' => (int_of_pos p' << 1) lor 1 end.
Fixpoint pos_of_int_aux (fuel : nat) (x : int) : positive :=
  match fuel with
  | O => 1
  | S f => if x <=? 1 then 1%positive else
           let p := pos_of_int_aux f (x >> 1) in
           if (x land 1) =? 1 then xI p else xO p
  end.
Definition pos_of_int (x : int) : positive := pos_of_int_aux 64 x.

Fixpoint popcount (r : list bool) : int :=
  match r with [] => 0 | b :: r' => if b then popcount r' + 1 else popcount r' end.

Definition column (R : rel) (l : nat) : list bool := map (fun r => nth l r false) R.

(** [renamed]: the mask with each frontier label j replaced by its name. *)
Fixpoint ren_aux (known : list (nat * nat)) (r : list bool) (j : nat) (acc : int) : int :=
  match r with
  | [] => acc
  | b :: r' =>
    ren_aux known r' (S j)
      (if b then match assoc_find j known with Some y => acc lor (1 << int_of_nat y) | None => acc end
       else acc)
  end.
Definition renamed known r := ren_aux known r 0 0.

Definition sig (known : list (nat * nat)) (H V : rel) (l : nat) : int :=
  let h := nth l H [] in let hi := column H l in let v := nth l V [] in let vi := column V l in
  renamed known h lor (renamed known hi << 8) lor (renamed known v << 16) lor (renamed known vi << 24)
  lor (popcount h << 32) lor (popcount hi << 36) lor (popcount v << 40) lor (popcount vi << 44).

Definition sig_lt (x y : int * nat) : bool :=
  (fst x <? fst y) || ((fst x =? fst y) && Nat.ltb (snd x) (snd y)).

Fixpoint insert_sorted (x : int * nat) (l : list (int * nat)) : list (int * nat) :=
  match l with [] => [x] | y :: l' => if sig_lt y x then y :: insert_sorted x l' else x :: l end.

Definition first_names (frl : list nat) : list (nat * nat) * nat :=
  fold_left (fun acc l => let '(a, m) := acc in
                          match assoc_find l a with Some _ => acc | None => ((l, m) :: a, S m) end)
            frl ([], O).

(** The renaming of wt_lazy's state key: frontier labels by first appearance, the other used
    labels sorted by signature, unused labels fixed. Returns (nu, inverse of nu). *)
Definition compute_nu (n k : nat) (frl : list nat) (H V : rel) : list nat * list nat :=
  let '(known, m0) := first_names frl in
  let rest := filter (fun l => match assoc_find l known with Some _ => false | None => true end) (seq 0 k) in
  let sorted := fold_left (fun acc l => insert_sorted (sig known H V l, l) acc) rest [] in
  let '(full, _) := fold_left (fun acc x => let '(a, m) := acc in ((snd x, m) :: a, S m)) sorted (known, m0) in
  let nu := map (fun l => if Nat.ltb l k then match assoc_find l full with Some y => y | None => l end else l)
                (seq 0 n) in
  let inv := map (fun x => index_of (x, O) (map (fun y => (y, O)) nu) O) (seq 0 n) in
  (nu, inv).

Local Close Scope uint63_scope.

(** A renaming of 0..n-1 is valid: nu and inv are inverse bijections that fix k..n-1. *)
Definition perm_ok (n k : nat) (nu inv : list nat) : bool :=
  forallb (fun i => Nat.ltb (nth i nu 0) n && Nat.eqb (nth (nth i nu 0) inv 0) i
                    && implb (Nat.leb k i) (Nat.eqb (nth i nu 0) i)) (seq 0 n) &&
  forallb (fun x => Nat.ltb (nth x inv 0) n && Nat.eqb (nth (nth x inv 0) nu 0) x
                    && implb (Nat.leb k x) (Nat.eqb (nth x inv 0) x)) (seq 0 n).

(** The repeat-skip state of a node, after renaming. *)
Record rst := mkR { r_pos : positive; r_k : nat; r_fr : list nat; r_H : rel; r_V : rel }.

Definition rst_eqb (x y : rst) : bool :=
  Pos.eqb (r_pos x) (r_pos y) && Nat.eqb (r_k x) (r_k y) && list_eqb (r_fr x) (r_fr y) &&
  rel_eqb (r_H x) (r_H y) && rel_eqb (r_V x) (r_V y).

Definition rst_of (n : nat) (e : entry) (k : nat) (lm : PM.t nat) (H V : rel) : option rst :=
  let frl := map (lab lm) (e_front e) in
  let '(nu, inv) := compute_nu n k frl H V in
  if perm_ok n k nu inv
  then Some (mkR (e_key e) k (map (fun l => nth l nu 0) frl) (rrename n inv H) (rrename n inv V))
  else None.

(** ** Packing states and relations into integers *)

Local Open Scope uint63_scope.

Record skey := mkK { k0 : int; k1 : int; k2 : int; k3 : int; k4 : int; k5 : int }.

Fixpoint pack3 (cnt : nat) (l : list nat) (sh : int) (acc : int) : int * list nat :=
  match cnt, l with
  | S c, x :: l' => pack3 c l' (sh + 3) (acc lor (int_of_nat x << sh))
  | _, _ => (acc, l)
  end.

Fixpoint unpack3 (cnt : nat) (w : int) : list nat :=
  match cnt with O => [] | S c => nat_of_small (w land 7) :: unpack3 c (w >> 3) end.

Fixpoint bits_row (r : list bool) (sh : int) (acc : int) : int :=
  match r with [] => acc | b :: r' => bits_row r' (sh + 1) (if b then acc lor (1 << sh) else acc) end.

Fixpoint rbits_aux (n : int) (R : rel) (sh : int) (acc : int) : int :=
  match R with [] => acc | r :: R' => rbits_aux n R' (sh + n) (bits_row r sh acc) end.
Definition rbits (n : nat) (R : rel) : int := rbits_aux (int_of_nat n) R 0 0.

Fixpoint unbits_row (cnt : nat) (w : int) : list bool :=
  match cnt with O => [] | S c => ((w land 1) =? 1) :: unbits_row c (w >> 1) end.
Fixpoint unbits (n : nat) (rows : nat) (w : int) : rel :=
  match rows with O => [] | S r => unbits_row n w :: unbits n r (w >> int_of_nat n) end.

(** The frontier takes up to 60 labels of 3 bits, in three words. *)
Definition enc (n : nat) (x : rst) : skey :=
  let len := List.length (r_fr x) in
  let '(w1, rest) := pack3 20 (r_fr x) 0 0 in
  let '(w2, rest) := pack3 20 rest 0 0 in
  let '(w3, _) := pack3 20 rest 0 0 in
  mkK (int_of_pos (r_pos x) lor (int_of_nat (r_k x) << 10) lor (int_of_nat len << 14))
      w1 w2 w3 (rbits n (r_H x)) (rbits n (r_V x)).

Definition dec (n : nat) (x : skey) : rst :=
  let len := nat_of_small ((k0 x >> 14) land 63) in
  mkR (pos_of_int (k0 x land 1023)) (nat_of_small ((k0 x >> 10) land 15))
      (unpack3 (Nat.min len 20) (k1 x) ++ unpack3 (Nat.min (len - 20) 20) (k2 x) ++ unpack3 (len - 40) (k3 x))
      (unbits n n (k4 x)) (unbits n n (k5 x)).

Definition skey_eqb (x y : skey) : bool :=
  (k0 x =? k0 y) && (k1 x =? k1 y) && (k2 x =? k2 y) && (k3 x =? k3 y) && (k4 x =? k4 y) && (k5 x =? k5 y).

Definition hash_mask : int := 4194303. (* 2^22 - 1 *)

Definition skey_hash (x : skey) : positive :=
  let h := (k0 x * 40503) lxor (k1 x * 2654435761) lxor (k2 x * 2246822519)
           lxor (k3 x * 374761393) lxor (k4 x * 3266489917) lxor (k5 x * 668265263) in
  pos_of_int (((h lxor (h >> 29)) land hash_mask) + 1).

(** ** The certificate stream *)

Record reader := mkRd { rd_chunks : list (list int); rd_cur : int; rd_left : int; rd_cnt : int }.

Definition read_byte (r : reader) : int * reader :=
  if rd_left r =? 0 then
    match rd_chunks r with
    | (w :: ws) :: cs => (w land 255, mkRd (ws :: cs) (w >> 8) 6 (rd_cnt r + 1))
    | [] :: cs => match cs with
                  | (w :: ws) :: cs' => (w land 255, mkRd (ws :: cs') (w >> 8) 6 (rd_cnt r + 1))
                  | _ => (0, mkRd [] 0 0 (rd_cnt r + 1))
                  end
    | [] => (0, mkRd [] 0 0 (rd_cnt r + 1))
    end
  else (rd_cur r land 255, mkRd (rd_chunks r) (rd_cur r >> 8) (rd_left r - 1) (rd_cnt r + 1)).

Fixpoint read_token_aux (fuel : nat) (r : reader) (sh acc : int) : int * reader :=
  match fuel with
  | O => (acc, r)
  | S f => let '(b, r') := read_byte r in
           let acc' := acc lor ((b land 127) << sh) in
           if (b land 128) =? 0 then (acc', r') else read_token_aux f r' (sh + 7) acc'
  end.
Definition read_token (r : reader) : int * reader := read_token_aux 5 r 0 0.

(** ** Caches of the answers per relation pair (open addressing, no proof needed)

    A slot holds (a, b, generation, value). Clearing a cache is starting a new generation:
    slots of older generations count as empty. *)

Definition slot := (int * int * int * int)%type.
Definition empty_slot : slot := (0, 0, max_int, 0).

(** Primitive arrays hold at most 2^22 - 1 cells, so a cache is an array of arrays of 2^20 slots. *)
Definition cache := array (array slot).
Definition cget (t : cache) (h : int) : slot := (t.[h >> 20]).[h land 1048575].
Definition cset (t : cache) (h : int) (v : slot) : cache :=
  let o := h >> 20 in t.[o <- (t.[o]).[h land 1048575 <- v]].
Definition cmake (size : int) : cache :=
  let inner := if size <=? 1048576 then size else 1048576 in
  let outer := if size <=? 1048576 then 1 else size >> 20 in
  fst (fold_left (fun acc _ => let '(t, i) := acc in (t.[i <- PArray.make inner empty_slot], i + 1))
                 (repeat tt (nat_of_int outer)) (PArray.make outer (PArray.make 1 empty_slot), 0)).

(** [Some (Some v, i)]: found with value v at i; [Some (None, i)]: free slot i. *)
Fixpoint probe (fuel : nat) (t : cache) (mask gen h a b : int) : option (option int * int) :=
  match fuel with
  | O => None
  | S f => let '(x, y, g, v) := cget t h in
           if negb (g =? gen) then Some (None, h)
           else if (x =? a) && (y =? b) then Some (Some v, h)
           else probe f t mask gen ((h + 1) land mask) a b
  end.

Definition rhash (mask a b : int) : int :=
  let h := (a * 2654435761) lxor (b * 40503) lxor (a >> 31) in (h lxor (h >> 23)) land mask.

Definition cfind (t : cache) (mask gen a b : int) : option (option int * int) :=
  probe 4000 t mask gen (rhash mask a b) a b.

Local Close Scope uint63_scope.

(** ** Tori *)

Record grid := mkG { ga : nat; gb : nat; gs : nat; gc : list nat }.
Definition gcell (g : grid) (r c : nat) : nat := nth (r * gb g + c) (gc g) 0.
Definition grid_h (g : grid) : list (nat * nat) :=
  flat_map (fun r => map (fun c => (gcell g r c, gcell g r ((c + 1) mod gb g))) (seq 0 (gb g))) (seq 0 (ga g)).
Definition grid_v (g : grid) : list (nat * nat) :=
  flat_map (fun r => map (fun c => (gcell g r c,
              if Nat.ltb (r + 1) (ga g) then gcell g (r + 1) c else gcell g 0 ((c + gs g) mod gb g)))
            (seq 0 (gb g))) (seq 0 (ga g)).
Definition grid_wf (n : nat) (g : grid) : bool :=
  Nat.leb 1 (ga g) && Nat.leb 1 (gb g) && Nat.ltb (gs g) (gb g) &&
  Nat.eqb (List.length (gc g)) (ga g * gb g) && forallb (fun x => Nat.ltb x n) (gc g).

Definition pair_dec : forall x y : nat * nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** A torus claim carries the proof that its pairs come from a well-formed torus grid. *)
Record ctorus (n : nat) := mkT {
  t_h : list (nat * nat); t_v : list (nat * nat);
  t_ok : exists g, grid_wf n g = true /\ (forall p, In p (grid_h g) -> In p t_h)
                                     /\ (forall p, In p (grid_v g) -> In p t_v) }.

Lemma mk_ctorus_ok (n : nat) (g : grid) : grid_wf n g = true ->
  exists g', grid_wf n g' = true /\ (forall p, In p (grid_h g') -> In p (nodup pair_dec (grid_h g)))
                                 /\ (forall p, In p (grid_v g') -> In p (nodup pair_dec (grid_v g))).
Proof.
  intros E. exists g. split; [exact E|]. split; intros p Hp; apply nodup_In; exact Hp.
Qed.

Definition mk_ctorus (n : nat) (g : grid) : option (ctorus n) :=
  match grid_wf n g as b return grid_wf n g = b -> option (ctorus n) with
  | true => fun E => Some (mkT n (nodup pair_dec (grid_h g)) (nodup pair_dec (grid_v g)) (mk_ctorus_ok n g E))
  | false => fun _ => None
  end eq_refl.

Definition grid_of_ints (l : list int) : grid :=
  match l with
  | a :: b :: s :: cs => mkG (nat_of_int a) (nat_of_int b) (nat_of_int s) (map nat_of_int cs)
  | _ => mkG 0 0 0 []
  end.

Definition build_tori (n : nat) (len : int) (tl : list (list (list int))) : array (option (ctorus n)) :=
  fst (fold_left (fun acc chunk =>
         fold_left (fun acc2 l => let '(arr, i) := acc2 in
                      (arr.[i <- mk_ctorus n (grid_of_ints l)], (i + 1)%uint63)) chunk acc)
       tl (PArray.make len None, 0%uint63)).

Definition torus_ok {n} (tor : array (option (ctorus n))) (ans : int) (H V : rel) : bool :=
  if (ans <? 2)%uint63 then false else
  match tor.[(ans - 2)%uint63] with
  | Some t => rincl (t_h n t) H && rincl (t_v n t) V
  | None => false
  end.

(** ** The walk state *)

(** [w_gen]: the current cache generation. [w_seen]: repeat-skip keys. [w_closed]: relation
    pairs whose closed claim has been verified. [w_rec]: the prefixes recorded at reset nodes,
    newest first. *)
Record wst := mkW {
  w_rd : reader; w_rel : cache; w_gate : cache; w_fin : cache; w_gen : int;
  w_seen : PM.t (list skey); w_closed : PM.t (list (rel * rel)); w_rec : list (list nat) }.

Definition set_rd (s : wst) (r : reader) : wst :=
  mkW r (w_rel s) (w_gate s) (w_fin s) (w_gen s) (w_seen s) (w_closed s) (w_rec s).
Definition set_rel (s : wst) (t : cache) (r : reader) : wst :=
  mkW r t (w_gate s) (w_fin s) (w_gen s) (w_seen s) (w_closed s) (w_rec s).
Definition set_gate (s : wst) (t : cache) (r : reader) : wst :=
  mkW r (w_rel s) t (w_fin s) (w_gen s) (w_seen s) (w_closed s) (w_rec s).
Definition set_fin (s : wst) (t : cache) (r : reader) : wst :=
  mkW r (w_rel s) (w_gate s) t (w_gen s) (w_seen s) (w_closed s) (w_rec s).
Definition set_seen (s : wst) (m : PM.t (list skey)) : wst :=
  mkW (w_rd s) (w_rel s) (w_gate s) (w_fin s) (w_gen s) m (w_closed s) (w_rec s).
Definition set_closed (s : wst) (m : PM.t (list (rel * rel))) : wst :=
  mkW (w_rd s) (w_rel s) (w_gate s) (w_fin s) (w_gen s) (w_seen s) m (w_rec s).
Definition push_rec (s : wst) (p : list nat) : wst :=
  mkW (w_rd s) (w_rel s) (w_gate s) (w_fin s) (w_gen s) (w_seen s) (w_closed s) (p :: w_rec s).
(** Clearing all tables, as check_cert.py does at a reset: a new cache generation, no seen keys.
    Verified closed relations are kept. *)
Definition clear (s : wst) : wst :=
  mkW (w_rd s) (w_rel s) (w_gate s) (w_fin s) (w_gen s + 1)%uint63 (PM.empty _) (w_closed s) (w_rec s).

Inductive seen_res := SHit | SBad | SMiss.

Fixpoint bucket_find (b : list skey) (x : skey) : option skey :=
  match b with [] => None | y :: b' => if skey_eqb x y then Some y else bucket_find b' x end.

Definition bucket (m : PM.t (list skey)) (h : positive) : list skey :=
  match PM.find h m with Some b => b | None => [] end.

Definition seen_find (n : nat) (m : PM.t (list skey)) (h : positive) (x : skey) (r : rst) : seen_res :=
  match bucket_find (bucket m h) x with
  | Some y => if rst_eqb (dec n y) r then SHit else SBad
  | None => SMiss
  end.

Definition chash (a b : int) : positive :=
  let h := ((a * 2654435761) lxor (b * 40503) lxor (a >> 29))%uint63 in
  pos_of_int (((h lxor (h >> 23)) land 1048575) + 1)%uint63.

Definition cbucket (m : PM.t (list (rel * rel))) (h : positive) : list (rel * rel) :=
  match PM.find h m with Some b => b | None => [] end.

Definition closed_mem (m : PM.t (list (rel * rel))) (h : positive) (H V : rel) : bool :=
  existsb (fun x => rel_eqb (fst x) H && rel_eqb (snd x) V) (cbucket m h).

Definition add_closed (s : wst) (h : positive) (H V : rel) : wst :=
  set_closed s (PM.add h ((H, V) :: cbucket (w_closed s) h) (w_closed s)).

Definition merges (R : rel) (lm : PM.t nat) (t : nat) (bk fw : list positive) : rel :=
  fold_left (fun R q => merge R t (lab lm q)) fw (fold_left (fun R p => merge R (lab lm p) t) bk R).

(** The one-merge supersets of a closed claim, in check_cert.py's order. *)
Definition pairs (n : nat) (H V : rel) : list (bool * nat * nat) :=
  flat_map (fun i => map (fun j => (true, i, j)) (filter (fun j => negb (rget H i j)) (seq 0 n))) (seq 0 n) ++
  flat_map (fun i => map (fun j => (false, i, j)) (filter (fun j => negb (rget V i j)) (seq 0 n))) (seq 0 n).

Definition sup (H V : rel) (p : bool * nat * nat) : rel * rel :=
  let '(isH, i, j) := p in if isH then (merge H i j, V) else (H, merge V i j).

Definition gate_flag : int := (1 << 40)%uint63.

Section Walk.
Variable n D : nat.
Variable imgs : list (list positive).
Variable tor : array (option (ctorus n)).
Variable mask gate : int.
Variable rtbl : PM.t (nat * nat * list (positive * nat)).
Variable rorder : list (nat * nat * positive).
Variable shards shard : nat.

Local Open Scope uint63_scope.

Definition refutes_rel (H V : rel) : bool :=
  refute_top_t n (rget H) (rget V) D rorder (4 * (n + 2) * (D * D))%nat rtbl.

(** A claim [tok] for (H, V) holds: a torus implied by them, or a verified closed relation. *)
Definition settled_ok (s : wst) (tok : int) (H V : rel) : bool :=
  if tok =? 1 then closed_mem (w_closed s) (chash (rbits n H) (rbits n V)) H V
  else torus_ok tor tok H V.

(** The cached answer for (a, b) in [t], or the next token, stored. [true]: freshly read. *)
Definition cread (t : cache) (gen : int) (rd : reader) (a b : int) : option (bool * int * cache * reader) :=
  match cfind t mask gen a b with
  | None => None
  | Some (Some v, _) => Some (false, v, t, rd)
  | Some (None, i) => let '(tok, rd') := read_token rd in Some (true, tok, cset t i (a, b, gen, tok), rd')
  end.

Definition rel_answer (s : wst) (a b : int) : option (bool * int * wst) :=
  match cread (w_rel s) (w_gen s) (w_rd s) a b with
  | None => None
  | Some (fr, v, t, rd) => Some (fr, v, set_rel s t rd)
  end.

Definition fin_answer (s : wst) (a b : int) : option (bool * int * wst) :=
  match cread (w_fin s) (w_gen s) (w_rd s) a b with
  | None => None
  | Some (fr, v, t, rd) => Some (fr, v, set_fin s t rd)
  end.

(** The gate table: a visit count, or [gate_flag + token] once a token has been read. At a
    node ([visit]) the count goes up and a token is read when it reaches [gate]; in a closed
    claim a token is read at once. *)
Definition gate_answer (visit : bool) (s : wst) (a b : int) : option (bool * int * wst) :=
  if visit && (gate =? 0) then Some (false, 0, s) else
  match cfind (w_gate s) mask (w_gen s) a b with
  | None => None
  | Some (o, i) =>
    let v := match o with Some v => v | None => 0 end in
    if gate_flag <=? v then Some (false, v - gate_flag, s) else
    if visit && (v + 1 <? gate) then Some (false, 0, set_gate s (cset (w_gate s) i (a, b, w_gen s, v + 1)) (w_rd s))
    else let '(tok, rd) := read_token (w_rd s) in
         Some (true, tok, set_gate s (cset (w_gate s) i (a, b, w_gen s, gate_flag + tok)) rd)
  end.

Local Close Scope uint63_scope.

(** The answer of a superset in a closed claim: the cached answer, or a fresh token that is
    claimed at once; it must not be 0. *)
Definition sup_answer (cl : int -> rel -> rel -> wst -> option wst) (H V : rel) (s : wst) : option (int * wst) :=
  let a := rbits n H in let b := rbits n V in
  match rel_answer s a b with None => None | Some (fr, tok, s1) =>
  if fr then (if (tok =? 0)%uint63 then None else option_map (fun s => (tok, s)) (cl tok H V s1))
  else if negb (tok =? 0)%uint63 then Some (tok, s1)
  else match gate_answer false s1 a b with None => None | Some (fr2, g, s2) =>
    if (g =? 0)%uint63 then None
    else if fr2 then option_map (fun s => (g, s)) (cl g H V s2) else Some (g, s2) end
  end.

Fixpoint supers (cl : int -> rel -> rel -> wst -> option wst) (H V : rel) (ps : list (bool * nat * nat))
  (done : list (rel * rel)) (s : wst) : option wst :=
  match ps with
  | [] => Some s
  | p :: ps' =>
    let '(H', V') := sup H V p in
    if existsb (fun x => rel_eqb (fst x) H' && rel_eqb (snd x) V') done then supers cl H V ps' done s else
    match sup_answer cl H' V' s with
    | None => None
    | Some (tok, s1) => if settled_ok s1 tok H' V' then supers cl H V ps' ((H', V') :: done) s1 else None
    end
  end.

(** Check a freshly read claim. A closed claim (1): (H, V) admits no DxD square, and every
    one-merge superset is settled. Torus claims are checked where they are used. *)
Fixpoint claim (fuel : nat) (tok : int) (H V : rel) (s : wst) : option wst :=
  match fuel with
  | O => None
  | S f =>
    if (tok =? 1)%uint63 then
      if refutes_rel H V then
        match supers (claim f) H V (pairs n H V) [] s with
        | None => None
        | Some s' => Some (add_closed s' (chash (rbits n H) (rbits n V)) H V)
        end
      else None
    else Some s
  end.

Definition cl_top := claim (2 * n * n + 2).

Definition fresh_claim (fr : bool) (tok : int) (H V : rel) (s : wst) : option wst :=
  if fr && negb (tok =? 0)%uint63 then cl_top tok H V s else Some s.

(** The merges of a new cell change nothing when every forced pair is already related. *)
Definition unchanged (R : rel) (lm : PM.t nat) (t : nat) (bk fw : list positive) : bool :=
  forallb (fun p => rget R (lab lm p) t) bk && forallb (fun q => rget R t (lab lm q)) fw.

(** Walk the children t = 0, 1, ... of a node in order, threading the state. The flag passed
    down says the child's relations equal this node's, so its cached answer is this node's: 0,
    unless the tables were cleared in between (see [e_deep]). *)
Fixpoint loop_children (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) (e : entry) (k : nat)
  (lm : PM.t nat) (H V : rel) (ts : list nat) (s : wst) : option wst :=
  match ts with
  | [] => Some s
  | t :: ts' =>
    match w (unchanged H lm t (e_left e) (e_right e) && unchanged V lm t (e_up e) (e_down e))
            (if Nat.eqb t k then S k else k) (PM.add (e_key e) t lm)
            (merges H lm t (e_left e) (e_right e)) (merges V lm t (e_up e) (e_down e)) s with
    | None => None
    | Some s' => loop_children w e k lm H V ts' s'
    end
  end.

(** The answer of a node: from the relation table, then the gate, then at a complete fill the
    final table; each freshly read claim is checked at once. *)
Definition node_answer (e : entry) (same : bool) (H V : rel) (s : wst) : option (int * wst) :=
  let a := rbits n H in let b := rbits n V in
  match (if same && e_deep e then Some (false, 0%uint63, s) else rel_answer s a b) with None => None | Some (fr1, ans1, s1) =>
  match fresh_claim fr1 ans1 H V s1 with None => None | Some s2 =>
  match (if (ans1 =? 0)%uint63 then gate_answer true s2 a b else Some (false, ans1, s2)) with None => None | Some (fr3, ans3, s3) =>
  match fresh_claim fr3 ans3 H V s3 with None => None | Some s4 =>
  match (if (ans3 =? 0)%uint63 && e_full e then fin_answer s4 a b else Some (false, ans3, s4)) with None => None | Some (fr5, ans5, s5) =>
  match fresh_claim fr5 ans5 H V s5 with None => None | Some s6 => Some (ans5, s6)
  end end end end end end.

(** One node: a leaf if its answer is a claim, which must hold; else the repeat skip, then
    the children. *)
Definition node_body (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) (e : entry)
  (same : bool) (k : nat) (lm : PM.t nat) (H V : rel) (s : wst) : option wst :=
  match node_answer e same H V s with None => None | Some (ans, s6) =>
  if negb (ans =? 0)%uint63 then (if settled_ok s6 ans H V then Some s6 else None) else
  if e_full e then None else
  match rst_of n e k lm H V with None => None | Some r =>
  let x := enc n r in let h := skey_hash x in
  match seen_find n (w_seen s6) h x r with
  | SHit => Some s6
  | SBad => None
  | SMiss =>
    if rst_eqb (dec n x) r
    then loop_children w e k lm H V (seq 0 (S (Nat.min k (n - 1)))) (set_seen s6 (PM.add h (x :: bucket (w_seen s6) h) (w_seen s6)))
    else None
  end end end.

(** At a reset node the labels of cells 0..P-1 are recorded and the tables cleared; the node is
    walked here only if its index (from 1) is [shard] modulo [shards]. *)
Fixpoint walk (fuel : nat) (tbl : list entry) (same : bool) (k : nat) (lm : PM.t nat) (H V : rel) (s : wst)
  {struct fuel} : option wst :=
  match fuel with O => None | S fuel' =>
  match tbl with [] => None | e :: tbl' =>
  if sym_skip imgs (e_key e) lm then Some s else
  if e_reset e then
    let s0 := clear (push_rec s (map (lab lm) (e_pre e))) in
    if Nat.eqb (List.length (w_rec s0) mod shards) shard
    then option_map clear (node_body (walk fuel' tbl') e false k lm H V s0)
    else Some s0
  else node_body (walk fuel' tbl') e same k lm H V s
  end end.

End Walk.

(** ** The checker *)

Record cert := mkCert {
  c_n : nat; c_D : nat; c_reset : nat; c_shards : nat; c_shard : nat; c_gate : int;
  c_tree : list (list int); c_bytes : int;
  c_ntori : int; c_tori : list (list (list int));
  c_cache : int }.

Definition run (c : cert) : option wst :=
  let n := c_n c in let D := c_D c in
  let tor := build_tori n (c_ntori c) (c_tori c) in
  let s0 := mkW (mkRd (c_tree c) 0 0 0) (cmake (c_cache c)) (cmake (c_cache c)) (cmake (c_cache c)) 0%uint63
                (PM.empty _) (PM.empty _) [] in
  walk n D (images D) tor (c_cache c - 1)%uint63 (c_gate c) (mk_tbl D) (centre_order D) (c_shards c) (c_shard c)
       (S (S (D * D))) (table D (c_reset c)) false 0 (PM.empty _) (rempty n) (rempty n) s0.

Fixpoint lists_eqb (x y : list (list nat)) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => list_eqb a b && lists_eqb x' y'
  | _, _ => false
  end.

(** A shard passes: its walk succeeds, reads the whole certificate, and the prefixes it
    recorded at reset nodes, oldest first, are exactly [refs]. *)
Definition check (refs : list (list nat)) (c : cert) : bool :=
  Nat.leb 1 (c_n c) && Nat.ltb (c_shard c) (c_shards c) && Nat.leb (c_reset c) (c_D c * c_D c) &&
  match run c with
  | Some s => (rd_cnt (w_rd s) =? c_bytes c)%uint63 && lists_eqb (rev (w_rec s)) refs
  | None => false
  end.
