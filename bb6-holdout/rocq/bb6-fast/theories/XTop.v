(** The exact part of the checker for the step count: levels above the band carry their length and their cost as a polynomial
    in the offset, with coefficients kept modulo 2^315. In the proofs the coefficients are exact integers. *)
From Coq Require Import ZArith Lia Uint63 List Bool PArray.
Import ListNotations.
From BB6 Require Import Map Num Walk Big Vec.
From BF Require Import Ints HLines HCore HAbs HBand HTop XCost XCore XAbs XBand.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** ** Numbers modulo 2^315 *)
Definition of_Zl (z : Z) : list int :=
  let m := z mod PM in
  [of_Z (m mod P63); of_Z (m / P63 mod P63); of_Z (m / P63 / P63 mod P63); of_Z (m / P63 / P63 / P63 mod P63); of_Z (m / P63 / P63 / P63 / P63 mod P63)].

Lemma phi_ofZ_mod x : phi (of_Z (x mod P63)) = x mod P63.
Proof. rewrite of_Z_spec. rewrite wB63. apply Z.mod_mod. lia. Qed.

Lemma of_Zl_spec z : cong PM (bval (of_Zl z)) z.
Proof.
  unfold of_Zl. cbv zeta. cbn [bval]. rewrite !phi_ofZ_mod.
  change PM with (P63 * P63 * P63 * P63 * P63).
  set (m := z mod (P63 * P63 * P63 * P63 * P63)).
  assert (Hm : 0 <= m < P63 * P63 * P63 * P63 * P63) by (unfold m; apply Z.mod_pos_bound; lia).
  assert (Em : z = m + (z / (P63 * P63 * P63 * P63 * P63)) * (P63 * P63 * P63 * P63 * P63)) by (unfold m; Z.div_mod_to_equations; lia).
  exists (- (z / (P63 * P63 * P63 * P63 * P63))).
  set (q := z / (P63 * P63 * P63 * P63 * P63)) in *. clearbody m q.
  assert (E : m = m mod P63 + P63 * (m / P63 mod P63 + P63 * (m / P63 / P63 mod P63 + P63 * (m / P63 / P63 / P63 mod P63 + P63 * (m / P63 / P63 / P63 / P63 mod P63 + P63 * 0))))).
  { rewrite Z.mul_0_r, Z.add_0_r.
    rewrite (Z.mod_small (m / P63 / P63 / P63 / P63)) by (split; [apply Z.div_pos; [repeat apply Z.div_pos|]; lia|]; repeat rewrite Z.div_div by lia; apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod m P63 ltac:(lia)). pose proof (Z.div_mod (m / P63) P63 ltac:(lia)).
    pose proof (Z.div_mod (m / P63 / P63) P63 ltac:(lia)). pose proof (Z.div_mod (m / P63 / P63 / P63) P63 ltac:(lia)). lia. }
  rewrite <- E. lia.
Qed.

Definition lW (w : W) : list int := of_W w.
(** Small constants without big-number arithmetic. *)
Definition lz (z : Z) : list int :=
  if (0 <=? z) && (z <? 4611686018427387904) then [of_Z z]
  else if (-4611686018427387904 <=? z) && (z <? 0) then [of_Z (z + P63); ones; ones; ones; ones]
  else let w := w_of_z z in if (val w =? z) then of_W w else of_Zl z.
(** Literal constants as primitive ints: no conversion from Z when the checker runs. *)
Definition lzi (neg : bool) (k : int) : list int := if neg then [(0 - k)%uint63; ones; ones; ones; ones] else [k].
Definition ladd := vadd.
Definition lmul := vmul.

Lemma lc_add x y X Y : cong PM (bval x) X -> cong PM (bval y) Y -> cong PM (bval (ladd x y)) (X + Y).
Proof. intros H1 H2. eapply cong_trans; [apply vadd_spec|]. apply cong_add; assumption. Qed.
Lemma lc_mul x y X Y : cong PM (bval x) X -> cong PM (bval y) Y -> cong PM (bval (lmul x y)) (X * Y).
Proof. intros H1 H2. eapply cong_trans; [apply vmul_spec|]. apply cong_mul; assumption. Qed.
Lemma lc_W w : cong PM (bval (lW w)) (val w).
Proof. apply of_W_spec. Qed.
Lemma lc_z z : cong PM (bval (lz z)) z.
Proof.
  unfold lz. destruct ((0 <=? z) && (z <? 4611686018427387904)) eqn:C1.
  - apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    exists 0. cbn [bval]. rewrite of_Z_spec, wB63, Z.mod_small by lia. ring.
  - destruct ((-4611686018427387904 <=? z) && (z <? 0)) eqn:C3.
    2:{ cbv zeta. destruct (val (w_of_z z) =? z) eqn:E; [apply Z.eqb_eq in E; rewrite <- E at 2; apply of_W_spec|apply of_Zl_spec]. }
    apply andb_prop in C3. destruct C3 as [C3 C4]. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
    exists 1. cbn [bval]. rewrite of_Z_spec, wB63, Z.mod_small by lia. change (phi ones) with (P63 - 1). change PM with (P63 * P63 * P63 * P63 * P63). ring.
Qed.
Lemma lc_zi (neg : bool) (k : int) (z : Z) : ((0 <? phi k) && (phi k <? 4611686018427387904))%Z = true -> (if neg then - phi k else phi k) = z ->
  cong PM (bval (lzi neg k)) z.
Proof.
  intros B E. apply andb_prop in B. destruct B as [B1 B2]. apply Z.ltb_lt in B1, B2. subst z. unfold lzi. destruct neg.
  - exists 1. cbn [bval]. rewrite sub_spec, wB63. change (phi 0%uint63) with 0. rewrite <- (Z.mod_add (0 - phi k) 1 P63) by lia.
    rewrite Z.mod_small by lia. change (phi ones) with (P63 - 1). change PM with (P63 * P63 * P63 * P63 * P63). ring.
  - exists 0. cbn [bval]. ring.
Qed.
Lemma lc_if (b : bool) x y X Y : cong PM (bval x) X -> cong PM (bval y) Y -> cong PM (bval (if b then x else y)) (if b then X else Y).
Proof. destruct b; auto. Qed.
Lemma cong_eq m x y z : cong m x y -> y = z -> cong m x z.
Proof. intros H <-. exact H. Qed.

(** [lcg]: a list expression is congruent to the integer expression of the same shape; then [ring] closes the rest. *)
Ltac lcg_build := repeat match goal with
  | |- cong PM (bval (ladd _ _)) _ => eapply lc_add
  | |- cong PM (bval (lmul _ _)) _ => eapply lc_mul
  | |- cong PM (bval (lW _)) _ => apply lc_W
  | |- cong PM (bval (lz _)) _ => apply lc_z
  | |- cong PM (bval (lzi ?n ?k)) _ => let v := eval vm_compute in (if n then - phi k else phi k) in apply (lc_zi n k v); [vm_compute; reflexivity|vm_compute; reflexivity]
  | |- cong PM (bval (if _ then _ else _)) _ => eapply lc_if
  | H : cong PM (bval ?x) _ |- cong PM (bval ?x) _ => exact H
  end.
Ltac unfold_lets := repeat match goal with x := _ |- _ => progress (unfold x) end.
Ltac lcg := eapply cong_eq; [lcg_build|]; try (unfold_lets; ring).

Lemma Rconv4 a b a1 b1 n r a2 b2 n2 r2 : Reach a b a1 b1 n r -> a1 = a2 -> b1 = b2 -> n = n2 -> r = r2 -> Reach a b a2 b2 n2 r2.
Proof. intros H -> -> -> ->. exact H. Qed.

(** ** Levels with a cost *)
Record XLv := mkXL { xl : Lv; xlen : int; c0 : list int; c1 : list int; c2 : list int }.

Definition xlv_ok (z : Z) (L : XLv) : Prop :=
  lv_fits (xl L) = true /\ 1 <= val (lg (xl L)) /\ 0 <= val (lthr (xl L)) /\ val (la (xl L)) + val (lb (xl L)) = val (lbase (xl L)) + val (lc (xl L)) /\
  0 <= phi (xlen L) < 1099511627776 /\
  exists P0 P1 P2, cong PM (bval (c0 L)) P0 /\ cong PM (bval (c1 L)) P1 /\ cong PM (bval (c2 L)) P2 /\
  forall y, 0 <= y -> y mod 4 = 0 -> val (lthr (xl L)) <= val (la (xl L)) - (val (lg (xl L)) - 1) * y ->
    Reach z (val (lbase (xl L)) + y) (val (la (xl L)) - (val (lg (xl L)) - 1) * y) (val (lb (xl L)) + val (lg (xl L)) * y) (phi (xlen L)) (P0 + P1 * y + P2 * (y * y)).

Lemma xlv_lv z L : xlv_ok z L -> lv_ok z (xl L).
Proof.
  intros (H1 & H2 & H3 & H4 & _ & P0 & P1 & P2 & _ & _ & _ & HR). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  intros y Hy Hm Ht. exists (phi (xlen L)), (P0 + P1 * y + P2 * (y * y)). apply HR; assumption.
Qed.

(** The cost polynomial moved to a later base: offset d. *)
Definition xshift (L : XLv) (d : W) : list int * list int * list int :=
  let dl := lW d in let t := lmul (c2 L) dl in
  (ladd (c0 L) (lmul (ladd (c1 L) t) dl), ladd (c1 L) (ladd t t), c2 L).

Lemma xlv_at z L B a b : xlv_ok z L -> fits B = true -> val (lbase (xl L)) <= val B -> (val B - val (lbase (xl L))) mod 4 = 0 ->
  eval (xl L) B = Some (a, b) ->
  let '(e0, e1, e2) := xshift L (sub B (lbase (xl L))) in
  exists Q0 Q1 Q2, cong PM (bval e0) Q0 /\ cong PM (bval e1) Q1 /\ cong PM (bval e2) Q2 /\
  forall y, 0 <= y -> y mod 4 = 0 -> val (lthr (xl L)) <= val a - (val (lg (xl L)) - 1) * y ->
    Reach z (val B + y) (val a - (val (lg (xl L)) - 1) * y) (val b + val (lg (xl L)) * y) (phi (xlen L)) (Q0 + Q1 * y + Q2 * (y * y)).
Proof.
  intros HX HB Hl Hm He. pose proof HX as (HF & Hg & Ht & Hs & Hlen & P0 & P1 & P2 & C0 & C1 & C2 & HR).
  destruct (eval_spec _ B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  assert (Vd : val (sub B (lbase (xl L))) = val B - val (lbase (xl L))).
  { pose proof (lv_bounds _ HF) as (_ & _ & _ & B4 & _ & _). apply fits_spec in HB. apply val_sub. lia. }
  unfold xshift. cbv zeta. set (d := val B - val (lbase (xl L))) in *.
  exists (P0 + P1 * d + P2 * (d * d)), (P1 + 2 * P2 * d), P2.
  split; [lcg; rewrite ?Vd; ring|]. split; [lcg; rewrite ?Vd; ring|]. split; [exact C2|].
  intros y Hy Hmy Hth.
  destruct (mod0_ex _ Hm) as [k Ek]. destruct (mod0_ex _ Hmy) as [j Ej].
  assert (Hd0 : 0 <= d) by (unfold d; lia).
  assert (R := HR (d + y) ltac:(lia) ltac:(rewrite Ek, Ej; replace (4 * k + 4 * j) with (4 * (k + j)) by ring; apply ex_mod0)).
  assert (Hth' : val (lthr (xl L)) <= val (la (xl L)) - (val (lg (xl L)) - 1) * (d + y)) by (rewrite Va in Hth; fold d in Hth; lia).
  specialize (R Hth').
  replace (val B + y) with (val (lbase (xl L)) + (d + y)) by (unfold d; ring).
  rewrite Va, Vb. fold d.
  eapply Rconv4; [exact R|ring|ring|reflexivity|ring].
Qed.

(** ** Letters at a level, with their cost *)
Definition xchildD (L : XLv) (a b B : W) : XLv :=
  let '(e0, e1, e2) := xshift L (sub B (lbase (xl L))) in
  mkXL (childD (xl L) a b B) (xlen L + 1)%uint63
    (ladd e0 (ladd (lmul (lzi true 30) (lW a)) (lzi false 18))) (ladd e1 (lmul (lzi false 30) (ladd (lW (lg (xl L))) (lzi true 1)))) e2.
Definition xchildUV (L : XLv) (a b B : W) (isu : bool) : XLv :=
  let '(e0, e1, e2) := xshift L (sub B (lbase (xl L))) in
  let g := lW (lg (xl L)) in let s := ladd (lW a) (lW b) in
  let ka := if isu then lzi true 11 else lzi true 19 in let kb := if isu then lzi false 29 else lzi false 37 in
  let k0 := if isu then lzi false 13 else lzi true 29 in let mka := if isu then lzi false 11 else lzi false 19 in
  mkXL (if isu then childU (xl L) a b B else childV (xl L) a b B) (xlen L + 1)%uint63
    (ladd e0 (ladd (lmul (lzi false 4) (lmul (lW b) s)) (ladd (lmul ka (lW a)) (ladd (lmul kb (lW b)) k0))))
    (ladd e1 (ladd (lmul (lzi false 4) (ladd (lW b) (lmul g s))) (ladd (lmul mka (ladd g (lzi true 1))) (lmul kb g))))
    (ladd e2 (lmul (lzi false 4) g)).

Lemma xlen_succ (L : XLv) : 0 <= phi (xlen L) < 1099511627776 -> phi (xlen L) + 1 < 1099511627776 -> phi (xlen L + 1)%uint63 = phi (xlen L) + 1.
Proof. intros H1 H2. apply phi_of_cg; [apply cg_add; apply cg_refl|change (phi 1%uint63) with 1; lia]. Qed.

Lemma xlvD z L B a b : xlv_ok z L -> fits B = true -> val (lbase (xl L)) <= val B -> (val B - val (lbase (xl L))) mod 4 = 0 -> eval (xl L) B = Some (a, b) ->
  val a + 3 < val b -> lv_fits (childD (xl L) a b B) = true -> phi (xlen L) + 1 < 1099511627776 -> xlv_ok z (xchildD L a b B).
Proof.
  intros HX HB Hl Hm He Hlt Hf Hn.
  pose proof (lvD z (xl L) B a b (xlv_lv z L HX) HB Hl Hm He Hlt Hf) as [_ [Sg [St [Ss _]]]].
  pose proof HX as (HF & Hg & Ht & Hs & Hlen & _).
  destruct (eval_spec _ B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  pose proof (xlv_at z L B a b HX HB Hl Hm He) as XA.
  unfold xchildD. destruct (xshift L (sub B (lbase (xl L)))) as [[e0 e1] e2]. destruct XA as (Q0 & Q1 & Q2 & C0 & C1 & C2 & HR).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (V1 : val (add (add a a) (wc 6)) = 2 * val a + 6) by (rewrite val_dbl_add by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  assert (V2 : val (sub (sub b a) (wc 3)) = val b - val a - 3) by (rewrite val_sub_sub_c by (exact Fa || exact Fb || (vm_compute; reflexivity)); reflexivity).
  assert (V3 : val (sub (add (lg (xl L)) (lg (xl L))) (wc 1)) = 2 * val (lg (xl L)) - 1) by (rewrite val_dbl_sub by (exact Fg || (vm_compute; reflexivity)); reflexivity).
  assert (V5 : (val (lg (xl L)) = 1 /\ val (if eqb (lg (xl L)) (wc 1) then wc 0 else add (add (lthr (xl L)) (lthr (xl L))) (wc 6)) = 0) \/
                (val (if eqb (lg (xl L)) (wc 1) then wc 0 else add (add (lthr (xl L)) (lthr (xl L))) (wc 6)) = 2 * val (lthr (xl L)) + 6)).
  { destruct (eqb (lg (xl L)) (wc 1)) eqn:Eg.
    - left. apply eqb_spec_W in Eg. rewrite val_wc in Eg. split; [exact Eg|reflexivity].
    - right. rewrite val_dbl_add by (exact Fth || (vm_compute; reflexivity)). reflexivity. }
  split; [exact Hf|]. split; [exact Sg|]. split; [exact St|]. split; [exact Ss|]. cbn [xlen].
  rewrite (xlen_succ L Hlen Hn). split; [lia|].
  exists (Q0 + (-30) * val a + 18), (Q1 + 30 * (val (lg (xl L)) + -1)), Q2. cbn [c0 c1 c2].
  split; [lcg|]. split; [lcg|]. split; [exact C2|].
  unfold childD; cbn [xl la lb lg lbase lthr lc]. rewrite V1, V2, V3.
  intros y Hy Hmy Hth.
  assert (Tr : val (lthr (xl L)) <= val a - (val (lg (xl L)) - 1) * y).
  { destruct V5 as [(E1 & X)|X].
    - rewrite E1. replace (val a - (1 - 1) * y) with (val a) by ring. exact Vt.
    - rewrite X in Hth. lia. }
  pose proof (HR y Hy Hmy Tr) as R.
  assert (Ly : val a - (val (lg (xl L)) - 1) * y + 3 < val b + val (lg (xl L)) * y).
  { assert (0 <= (2 * val (lg (xl L)) - 1) * y) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R (XD _ _ Ly)) as R2.
  eapply Rconv4; [exact R2|ring|ring|ring|ring].
Qed.

Lemma xlvUV z L B a b (isu : bool) : xlv_ok z L -> fits B = true -> val (lbase (xl L)) <= val B -> (val B - val (lbase (xl L))) mod 4 = 0 -> eval (xl L) B = Some (a, b) ->
  val b mod 2 = 1 -> 5 <= val b -> val b + 1 <= val a -> (val (lg (xl L)) = 1 \/ val (lthr (xl L)) <= val b + 1) ->
  (isu = true -> (val a - val b + 5) mod 4 = 2) -> (isu = false -> (val a - val b + 5) mod 4 <> 2) ->
  lv_fits (if isu then childU (xl L) a b B else childV (xl L) a b B) = true -> phi (xlen L) + 1 < 1099511627776 -> xlv_ok z (xchildUV L a b B isu).
Proof.
  intros HX HB Hl Hm He Odd B5 Bab Thr Hu Hv Hf Hn.
  pose proof (lvUV z (xl L) B a b isu (xlv_lv z L HX) HB Hl Hm He Odd B5 Bab Thr Hu Hv Hf) as [_ [Sg [St [Ss _]]]].
  pose proof HX as (HF & Hg & Ht & Hs & Hlen & _).
  destruct (eval_spec _ B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  pose proof (xlv_at z L B a b HX HB Hl Hm He) as XA.
  unfold xchildUV. destruct (xshift L (sub B (lbase (xl L)))) as [[e0 e1] e2]. destruct XA as (Q0 & Q1 & Q2 & C0 & C1 & C2 & HR).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (Vg : val (add (lg (xl L)) (lg (xl L))) = 2 * val (lg (xl L))) by (rewrite val_add2 by exact Fg; ring).
  set (ka := if isu then -11 else -19). set (kb := if isu then 29 else 37). set (k0 := if isu then 13 else -29). set (mka := if isu then 11 else 19).
  assert (Emka : mka = - ka) by (unfold mka, ka; destruct isu; reflexivity).
  split; [exact Hf|]. split; [exact Sg|]. split; [exact St|]. split; [exact Ss|]. cbn [xlen].
  rewrite (xlen_succ L Hlen Hn). split; [lia|].
  set (g := val (lg (xl L))) in *. set (s := val a + val b).
  exists (Q0 + (4 * (val b * s) + (ka * val a + (kb * val b + k0)))), (Q1 + (4 * (val b + g * s) + (mka * (g + -1) + kb * g))), (Q2 + 4 * g). cbn [c0 c1 c2].
  split; [lcg|]. split; [lcg|]. split; [lcg|].
  intros y Hy Hmy Hth.
  assert (Hth2 : val b + 1 <= val a - (g - 1) * y - g * y).
  { destruct isu; [unfold childU in Hth|unfold childV in Hth]; cbn [xl la lb lg lbase lthr lc] in Hth; rewrite Vg in Hth;
      rewrite val_sub_add_c in Hth by (exact Fa || exact Fb || (vm_compute; reflexivity));
      [change (val (wc 12)) with 12 in Hth; change (phi 11%uint63) with 11 in Hth|change (val (wc 20)) with 20 in Hth; change (phi 19%uint63) with 19 in Hth];
      fold g in Hth; clear - Hth; lia. }
  assert (Tr : val (lthr (xl L)) <= val a - (g - 1) * y).
  { destruct Thr as [E1|E1].
    - rewrite E1. replace (val a - (1 - 1) * y) with (val a) by ring. exact Vt.
    - assert (0 <= g * y) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  pose proof (HR y Hy Hmy Tr) as R.
  destruct (mod0_ex _ Hmy) as [j Ej].
  assert (Gy : 0 <= g * y) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Od : (val b + g * y) mod 2 = 1).
  { rewrite Ej. replace (val b + g * (4 * j)) with (val b + (2 * (g * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Odd. }
  assert (Rs : forall c, (val a - (g - 1) * y - (val b + g * y) + 5) mod 4 = c -> (val a - val b + 5) mod 4 = c).
  { intros c X. rewrite <- X. rewrite Ej. replace (val a - (g - 1) * (4 * j) - (val b + g * (4 * j)) + 5) with (val a - val b + 5 + (- (2 * g - 1) * j) * 4) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (B1 : 5 <= val b + g * y) by lia. assert (B2 : val b + g * y + 1 <= val a - (g - 1) * y) by lia.
  destruct isu.
  - specialize (Hu eq_refl).
    assert (Hu' : (val a - (g - 1) * y - (val b + g * y) + 5) mod 4 = 2).
    { rewrite Ej in *. replace (val a - (g - 1) * (4 * j) - (val b + g * (4 * j)) + 5) with (val a - val b + 5 + (- (2 * g - 1) * j) * 4) by ring.
      rewrite Z.mod_add by lia. exact Hu. }
    pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R (XU _ _ Od Hu' B1 B2)) as R2.
    unfold childU; cbn [xl la lb lg lbase lthr lc]. rewrite Vg.
    rewrite val_sub_add_c by (exact Fa || exact Fb || (vm_compute; reflexivity)). rewrite val_dbl_sub by (exact Fb || (vm_compute; reflexivity)).
    change (phi 11%uint63) with 11. change (phi 4%uint63) with 4.
    eapply Rconv4; [exact R2|unfold_lets; ring|unfold_lets; ring|unfold_lets; ring|unfold_lets; ring].
  - specialize (Hv eq_refl).
    assert (Hv' : (val a - (g - 1) * y - (val b + g * y) + 5) mod 4 <> 2) by (intros X; apply Hv; apply Rs; exact X).
    pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R (XV _ _ Od Hv' B1 B2)) as R2.
    unfold childV; cbn [xl la lb lg lbase lthr lc]. rewrite Vg.
    rewrite val_sub_add_c by (exact Fa || exact Fb || (vm_compute; reflexivity)). rewrite val_dbl_sub by (exact Fb || (vm_compute; reflexivity)).
    change (phi 19%uint63) with 19. change (phi 8%uint63) with 8.
    eapply Rconv4; [exact R2|unfold_lets; ring|unfold_lets; ring|unfold_lets; ring|unfold_lets; ring].
Qed.

(** A level moved to its state at a later start. *)
Definition xrebase (L : XLv) (a b B : W) : XLv :=
  let '(e0, e1, e2) := xshift L (sub B (lbase (xl L))) in mkXL (rebase (xl L) a b B) (xlen L) e0 e1 e2.
Lemma xrebase_ok z L B a b : xlv_ok z L -> fits B = true -> val (lbase (xl L)) <= val B -> (val B - val (lbase (xl L))) mod 4 = 0 -> eval (xl L) B = Some (a, b) ->
  xlv_ok z (xrebase L a b B).
Proof.
  intros HX HB Hl Hm He.
  pose proof (rebase_ok z (xl L) B a b (xlv_lv z L HX) HB Hl Hm He) as [Hf [Sg [St [Ss _]]]].
  pose proof HX as (_ & _ & _ & _ & Hlen & _).
  pose proof (xlv_at z L B a b HX HB Hl Hm He) as XA.
  unfold xrebase. destruct (xshift L (sub B (lbase (xl L)))) as [[e0 e1] e2]. destruct XA as (Q0 & Q1 & Q2 & C0 & C1 & C2 & HR).
  split; [exact Hf|]. split; [exact Sg|]. split; [exact St|]. split; [exact Ss|]. split; [exact Hlen|].
  exists Q0, Q1, Q2. split; [exact C0|]. split; [exact C1|]. split; [exact C2|].
  unfold rebase; cbn [xl la lb lg lbase lthr lc xlen]. exact HR.
Qed.

(** ** Words that end in a reset, with their cost *)
Record XTerm := mkXT { xt : Term; tlen : int; t0 : list int; t1 : list int; t2 : list int }.

Definition xterm_sem (z : Z) (t : XTerm) : Prop :=
  term_sem z (xt t) /\
  (tok (xt t) = true -> 0 <= phi (tlen t) < 1099511627776 /\
   exists P0 P1 P2, cong PM (bval (t0 t)) P0 /\ cong PM (bval (t1 t)) P1 /\ cong PM (bval (t2 t)) P2 /\
   forall y, 0 <= y -> y mod 4 = 0 -> val (lthr (tL (xt t))) <= val (la (tL (xt t))) - (val (lg (tL (xt t))) - 1) * y ->
     val (lb (tL (xt t))) + val (lg (tL (xt t))) * y < val (la (tL (xt t))) - (val (lg (tL (xt t))) - 1) * y + 3 ->
     Reach z (val (lbase (tL (xt t))) + y) (phi (tna (xt t))) (val (lbase (tL (xt t))) + y + val (tD (xt t))) (phi (tlen t)) (P0 + P1 * y + P2 * (y * y))).

Definition xterm_of (L : XLv) : XTerm :=
  let t := term_of (xl L) in
  let a := lW (la (xl L)) in let b := lW (lb (xl L)) in let g := lW (lg (xl L)) in let h := ladd g (lzi true 1) in
  let K := if (tna t =? 6)%uint63 then lzi false 378 else lzi false 274 in
  mkXT t (xlen L + 1)%uint63
    (ladd (c0 L) (ladd (lmul (lzi false 2) (lmul a a)) (ladd (lmul (lzi false 6) (lmul b b)) (ladd (lmul (lzi false 39) a) (ladd (lmul (lzi true 9) b) K)))))
    (ladd (c1 L) (ladd (lmul (lzi true 4) (lmul a h)) (ladd (lmul (lzi false 12) (lmul b g)) (ladd (lmul (lzi true 39) h) (lmul (lzi true 9) g)))))
    (ladd (c2 L) (ladd (lmul (lzi false 2) (lmul h h)) (lmul (lzi false 6) (lmul g g)))).
Definition noxterm : XTerm := mkXT noterm 0 [] [] [].

Lemma xterm_of_ok z L : xlv_ok z L -> val (lb (xl L)) mod 2 = 0 -> fits (add (lc (xl L)) (wc 7)) = true -> fits (sub (lc (xl L)) (wc 2)) = true ->
  phi (xlen L) + 1 < 1099511627776 -> xterm_sem z (xterm_of L).
Proof.
  intros HX Ev F7 F2 Hn. split; [exact (term_of_ok z (xl L) (xlv_lv z L HX) Ev F7 F2)|]. intros _.
  pose proof HX as (HF & Hg & Ht & Hs & Hlen & P0 & P1 & P2 & C0 & C1 & C2 & HR).
  pose proof (lv_bounds _ HF) as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (Vs : val (sub (la (xl L)) (lb (xl L))) = val (la (xl L)) - val (lb (xl L))) by (apply val_sub2; assumption).
  unfold xterm_of. cbn [xt tlen t0 t1 t2]. unfold term_of. cbn [tL tna tok]. rewrite (xlen_succ L Hlen Hn). split; [lia|].
  set (A := val (la (xl L))). set (Bb := val (lb (xl L))). set (g := val (lg (xl L))).
  destruct (low2 (sub (la (xl L)) (lb (xl L))) =? 2)%uint63 eqn:C.
  - change (6 =? 6)%uint63 with true. cbv iota.
    exists (P0 + (2 * (A * A) + (6 * (Bb * Bb) + (39 * A + (-9 * Bb + 378))))), (P1 + (-4 * (A * (g + -1)) + (12 * (Bb * g) + (-39 * (g + -1) + -9 * g)))),
           (P2 + (2 * ((g + -1) * (g + -1)) + 6 * (g * g))).
    split; [lcg|]. split; [lcg|]. split; [lcg|].
    intros y Hy Hm Hth Hlt. unfold tD. cbn [tna tL]. change (6 =? 6)%uint63 with true. cbv iota.
    rewrite val_add_c by (exact Fc || (vm_compute; reflexivity)). change (phi 7%uint63) with 7.
    apply eqb_true in C. rewrite low2_mod, Vs in C. change (phi 2%uint63) with 2 in C.
    pose proof (HR y Hy Hm Hth) as R.
    destruct (mod0_ex _ Hm) as [j Ej].
    assert (E1 : (Bb + g * y) mod 2 = 0).
    { rewrite Ej. replace (Bb + g * (4 * j)) with (Bb + (2 * (g * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Ev. }
    assert (E2 : (A - (g - 1) * y - (Bb + g * y)) mod 4 = 2).
    { rewrite Ej. replace (A - (g - 1) * (4 * j) - (Bb + g * (4 * j))) with (A - Bb + (- (2 * g - 1) * j) * 4) by ring. rewrite Z.mod_add by lia. exact C. }
    pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R (XW _ _ E1 Hlt E2)) as R2.
    change (phi 6%uint63) with 6.
    eapply Rconv4; [exact R2|reflexivity|unfold_lets; lia|unfold_lets; ring|unfold_lets; ring].
  - change (22 =? 6)%uint63 with false. cbv iota.
    exists (P0 + (2 * (A * A) + (6 * (Bb * Bb) + (39 * A + (-9 * Bb + 274))))), (P1 + (-4 * (A * (g + -1)) + (12 * (Bb * g) + (-39 * (g + -1) + -9 * g)))),
           (P2 + (2 * ((g + -1) * (g + -1)) + 6 * (g * g))).
    split; [lcg|]. split; [lcg|]. split; [lcg|].
    intros y Hy Hm Hth Hlt. unfold tD. cbn [tna tL]. change (22 =? 6)%uint63 with false. cbv iota.
    rewrite val_sub_c by (exact Fc || (vm_compute; reflexivity)). change (phi 2%uint63) with 2.
    assert (C' : (A - Bb) mod 4 <> 2).
    { intros X. unfold A, Bb in X. rewrite <- Vs, <- low2_mod in X. assert (Y : low2 (sub (la (xl L)) (lb (xl L))) = 2%uint63) by (apply to_Z_inj; exact X). rewrite Y in C. discriminate. }
    pose proof (HR y Hy Hm Hth) as R.
    destruct (mod0_ex _ Hm) as [j Ej].
    assert (E1 : (Bb + g * y) mod 2 = 0).
    { rewrite Ej. replace (Bb + g * (4 * j)) with (Bb + (2 * (g * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Ev. }
    assert (E2 : (A - (g - 1) * y - (Bb + g * y)) mod 4 <> 2).
    { rewrite Ej. replace (A - (g - 1) * (4 * j) - (Bb + g * (4 * j))) with (A - Bb + (- (2 * g - 1) * j) * 4) by ring. rewrite Z.mod_add by lia. exact C'. }
    pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R (XX _ _ E1 Hlt E2)) as R2.
    change (phi 22%uint63) with 22.
    eapply Rconv4; [exact R2|reflexivity|unfold_lets; lia|unfold_lets; ring|unfold_lets; ring].
Qed.

(** ** Whole words, for a detour *)
Definition xroot (z : int) (B : W) : XLv := mkXL (root z B) 0 [] [] [].
Lemma xroot_ok z B : fits B = true -> (phi z = 6 \/ phi z = 22) -> xlv_ok (phi z) (xroot z B).
Proof.
  intros HB Hz. pose proof (root_ok z B HB Hz) as [Hf [Hg [Ht [Hs _]]]].
  split; [exact Hf|]. split; [exact Hg|]. split; [exact Ht|]. split; [exact Hs|]. split; [change (phi (xlen (xroot z B))) with 0; lia|].
  exists 0, 0, 0. cbn [c0 c1 c2]. split; [exists 0; reflexivity|]. split; [exists 0; reflexivity|]. split; [exists 0; reflexivity|].
  intros y _ _ _. unfold xroot, root; cbn [xl la lb lg lbase xlen]. rewrite val_wc. change (phi 0%uint63) with 0. change (val (wc 1)) with 1.
  eapply Rconv4; [apply Reach_refl|ring|ring|reflexivity|ring].
Qed.

Fixpoint xwalk (f : nat) (L : XLv) : XTerm :=
  match f with
  | O => noxterm
  | S f =>
    if (1099511627000 <=? xlen L)%uint63 then noxterm else
    let L0 := xl L in
    match eval L0 (lbase L0) with
    | None => noxterm
    | Some (a, b) =>
      if ltb (add a (wc 3)) b then
        let c := childD L0 a b (lbase L0) in
        if lv_fits c then xwalk f (xchildD L a b (lbase L0)) else noxterm
      else if ltb b (wc 5) || negb (lv_fits (rebase L0 a b (lbase L0))) || eqb (add a (wc 3)) b then noxterm
      else if ((low2 b) land 1 =? 1)%uint63 then
        if eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L0) (wc 1) || leb (lthr L0) (add b (wc 1))) then noxterm
        else
          let isu := (low2 (add (sub a b) (wc 5)) =? 2)%uint63 in
          let c := if isu then childU L0 a b (lbase L0) else childV L0 a b (lbase L0) in
          if lv_fits c then xwalk f (xchildUV L a b (lbase L0) isu) else noxterm
      else
        if fits (add (lc L0) (wc 7)) && fits (sub (lc L0) (wc 2)) && (ltb b (add a (wc 3))) then xterm_of (xrebase L a b (lbase L0)) else noxterm
    end
  end.

Lemma noxterm_ok z : xterm_sem z noxterm.
Proof. split; [intros X; discriminate X|intros X; discriminate X]. Qed.

Lemma xwalk_sound f z : forall L, xlv_ok z L -> xterm_sem z (xwalk f L).
Proof.
  induction f as [|f IH]; intros L HL; [apply noxterm_ok|].
  cbn [xwalk].
  destruct (1099511627000 <=? xlen L)%uint63 eqn:Cn; [apply noxterm_ok|]. apply leb_false in Cn. change (phi 1099511627000%uint63) with 1099511627000 in Cn.
  pose proof HL as (HF & Hg & Ht & Hs & Hlen & _).
  assert (HB : fits (lbase (xl L)) = true).
  { unfold lv_fits in HF. repeat (apply andb_prop in HF; destruct HF as [HF ?]). assumption. }
  destruct (eval (xl L) (lbase (xl L))) as [[a b]|] eqn:He; [|apply noxterm_ok].
  destruct (eval_spec (xl L) (lbase (xl L)) a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  assert (M0 : (val (lbase (xl L)) - val (lbase (xl L))) mod 4 = 0) by (rewrite Z.sub_diag; reflexivity).
  assert (V3 : val (add a (wc 3)) = val a + 3) by (rewrite val_add_c by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  destruct (ltb (add a (wc 3)) b) eqn:C1.
  { destruct (lv_fits (childD (xl L) a b (lbase (xl L)))) eqn:Fc; [|apply noxterm_ok].
    apply IH. apply (xlvD z L (lbase (xl L)) a b HL HB ltac:(lia) M0 He); [|exact Fc|lia]. apply ltb_spec_W in C1. lia. }
  destruct (ltb b (wc 5) || negb (lv_fits (rebase (xl L) a b (lbase (xl L)))) || eqb (add a (wc 3)) b) eqn:C2; [apply noxterm_ok|].
  apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 C3].
  destruct ((low2 b) land 1 =? 1)%uint63 eqn:Od.
  - destruct (eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg (xl L)) (wc 1) || leb (lthr (xl L)) (add b (wc 1)))) eqn:C4; [apply noxterm_ok|].
    apply orb_false_iff in C4. destruct C4 as [C4 C6]. apply orb_false_iff in C4. destruct C4 as [_ C5].
    apply negb_false_iff in C5, C6. apply leb_spec_W in C5. rewrite val_add_c in C5 by (exact Fb || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in C5.
    assert (B5 : 5 <= val b) by (pose proof (ltb_false_W _ _ C2) as X; rewrite val_wc in X; exact X).
    destruct (lv_fits (if (low2 (add (sub a b) (wc 5)) =? 2)%uint63 then childU (xl L) a b (lbase (xl L)) else childV (xl L) a b (lbase (xl L)))) eqn:Fc; [|apply noxterm_ok].
    apply IH. apply (xlvUV z L (lbase (xl L)) a b _ HL HB ltac:(lia) M0 He); try assumption.
    + apply low2_odd. exact Od.
    + apply orb_prop in C6. destruct C6 as [C6|C6].
      * left. apply eqb_spec_W in C6. rewrite C6. reflexivity.
      * right. apply leb_spec_W in C6. rewrite val_add_c in C6 by (exact Fb || (vm_compute; reflexivity)). exact C6.
    + apply low2_u; assumption.
    + apply low2_v; assumption.
    + lia.
  - destruct (fits (add (lc (xl L)) (wc 7)) && fits (sub (lc (xl L)) (wc 2)) && (ltb b (add a (wc 3)))) eqn:C4; [|apply noxterm_ok].
    apply andb_prop in C4. destruct C4 as [C4 _]. apply andb_prop in C4. destruct C4 as [F7 F2].
    pose proof (xrebase_ok z L (lbase (xl L)) a b HL HB ltac:(lia) M0 He) as HR.
    apply xterm_of_ok; [exact HR| | | |].
    + unfold xrebase. destruct (xshift L (sub (lbase (xl L)) (lbase (xl L)))) as [[e0 e1] e2]. cbn [xl lb rebase]. apply low2_even. exact Od.
    + unfold xrebase. destruct (xshift L (sub (lbase (xl L)) (lbase (xl L)))) as [[e0 e1] e2]. cbn [xl lc rebase]. exact F7.
    + unfold xrebase. destruct (xshift L (sub (lbase (xl L)) (lbase (xl L)))) as [[e0 e1] e2]. cbn [xl lc rebase]. exact F2.
    + unfold xrebase. destruct (xshift L (sub (lbase (xl L)) (lbase (xl L)))) as [[e0 e1] e2]. cbn [xlen]. lia.
Qed.

(** ** Sums over rounds, exactly *)
Definition INV3 : Z := 22249864957509480024948142772599501193778172107881799686948350081481455476881672396072521738923.
Lemma inv3_ok x : cong PM (INV3 * (3 * x)) x.
Proof. exists x. change PM with 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768. change INV3 with 22249864957509480024948142772599501193778172107881799686948350081481455476881672396072521738923. ring. Qed.

Definition LINV3 : list int := Eval vm_compute in of_Zl INV3.
Lemma lc_INV3 : cong PM (bval LINV3) INV3.
Proof. exists 0. vm_compute. reflexivity. Qed.
Ltac lcg_build ::= repeat match goal with
  | |- cong PM (bval (ladd _ _)) _ => eapply lc_add
  | |- cong PM (bval (lmul _ _)) _ => eapply lc_mul
  | |- cong PM (bval (lW _)) _ => apply lc_W
  | |- cong PM (bval (lz _)) _ => apply lc_z
  | |- cong PM (bval (lzi ?n ?k)) _ => let v := eval vm_compute in (if n then - phi k else phi k) in apply (lc_zi n k v); [vm_compute; reflexivity|vm_compute; reflexivity]
  | |- cong PM (bval (if _ then _ else _)) _ => eapply lc_if
  | |- cong PM (bval LINV3) _ => apply lc_INV3
  | H : cong PM (bval ?x) _ |- cong PM (bval ?x) _ => exact H
  end.

Definition halve (x : W) : option W :=
  let q := adiv x (wc 2) in
  match mul_nn q (wc 2) with Some p => if eqb p x then Some q else None | None => None end.
Lemma halve_spec x q : halve x = Some q -> val q * 2 = val x.
Proof.
  unfold halve. cbv zeta. destruct (mul_nn (adiv x (wc 2)) (wc 2)) as [p|] eqn:M; [|discriminate].
  destruct (eqb p x) eqn:E; [|discriminate]. intros H. injection H as <-.
  destruct (mul_nn_spec _ _ _ M) as [V _]. apply eqb_spec_W in E. rewrite val_wc in V. change (phi 2%uint63) with 2 in V. lia.
Qed.

Definition sums (T : W) : option (list int * list int) :=
  let T1 := sub T (wc 1) in
  match (match halve T with Some h => Some (h, T1) | None => match halve T1 with Some h => Some (h, T) | None => None end end) with
  | Some (u, v) =>
    let s1l := lmul (lW u) (lW v) in
    Some (s1l, lmul LINV3 (lmul s1l (lW (sub (add T T) (wc 1)))))
  | None => None
  end.

Lemma sums_spec T s1l s2l : fits T = true -> 1 <= val T -> sums T = Some (s1l, s2l) ->
  cong PM (bval s1l) (s1 (Z.to_nat (val T))) /\ cong PM (bval s2l) (s2 (Z.to_nat (val T))).
Proof.
  intros F HT H. unfold sums in H. cbv zeta in H. apply fits_spec in F.
  assert (V1 : val (sub T (wc 1)) = val T - 1) by (rewrite val_sub; rewrite val_wc; change (phi 1%uint63) with 1; lia).
  assert (V2 : val (sub (add T T) (wc 1)) = 2 * val T - 1).
  { assert (X : val (add T T) = 2 * val T) by (rewrite val_add; lia). rewrite val_sub; rewrite ?X, val_wc; change (phi 1%uint63) with 1; lia. }
  pose proof (s1_form (Z.to_nat (val T))) as F1. pose proof (s2_form (Z.to_nat (val T))) as F2. rewrite T_nat in F1, F2 by lia.
  assert (Huv : forall u v, val u * val v * 2 = val T * (val T - 1) -> s1 (Z.to_nat (val T)) = val u * val v) by (intros u v X; lia).
  destruct (halve T) as [h|] eqn:Hh.
  - injection H as <- <-. pose proof (halve_spec _ _ Hh) as Eh.
    assert (S1 : s1 (Z.to_nat (val T)) = val h * val (sub T (wc 1))) by (apply Huv; rewrite V1, <- Eh; ring).
    split.
    + rewrite S1. lcg.
    + assert (S2 : s2 (Z.to_nat (val T)) * 3 = s1 (Z.to_nat (val T)) * (2 * val T - 1)) by lia.
      eapply cong_trans; [|apply (inv3_ok (s2 (Z.to_nat (val T))))]. rewrite Z.mul_comm with (n := 3), S2, S1.
      lcg. rewrite V2. ring.
  - destruct (halve (sub T (wc 1))) as [h|] eqn:Hh2; [|discriminate]. injection H as <- <-. pose proof (halve_spec _ _ Hh2) as Eh.
    assert (S1 : s1 (Z.to_nat (val T)) = val h * val T) by (apply Huv; rewrite <- V1, <- Eh; ring).
    split.
    + rewrite S1. lcg.
    + assert (S2 : s2 (Z.to_nat (val T)) * 3 = s1 (Z.to_nat (val T)) * (2 * val T - 1)) by lia.
      eapply cong_trans; [|apply (inv3_ok (s2 (Z.to_nat (val T))))]. rewrite Z.mul_comm with (n := 3), S2, S1.
      lcg. rewrite V2. ring.
Qed.

(** Rounds with a quadratic cost per round: the total in closed form. *)
Lemma xrounds z B D n0 A1 A2 A3 (T : Z) : 1 <= T ->
  (forall k, 0 <= k < T -> Reach z (B + k * D) z (B + (k + 1) * D) n0 (A1 + A2 * (k * D) + A3 * ((k * D) * (k * D)))) ->
  Reach z B z (B + T * D) (T * n0) (T * A1 + D * s1 (Z.to_nat T) * A2 + D * D * s2 (Z.to_nat T) * A3).
Proof.
  intros HT H. pose proof (rounds_poly z B 0 D n0 A1 A2 A3 (Z.to_nat T)) as R. rewrite T_nat in R by lia.
  assert (P : forall t, 0 <= t < T -> Reach z (B + 0 + t * D) z (B + 0 + (t + 1) * D) n0 (A1 + A2 * (0 + t * D) + A3 * ((0 + t * D) * (0 + t * D)))).
  { intros t Ht. rewrite !Z.add_0_r, !Z.add_0_l. exact (H t Ht). }
  specialize (R P). rewrite !Z.add_0_r in R.
  eapply Rconv4; [exact R|reflexivity|reflexivity|reflexivity|ring].
Qed.

Lemma int_ne (a b : int) : (a =? b)%uint63 = false -> a <> b.
Proof. intros H X. rewrite X, Uint63.eqb_refl in H. discriminate. Qed.

(** ** The state of a run, with the count and the cost so far *)
Record XSt := mkXS { qz : int; qB : W; qstat : int; qha : W; qd6 : XTerm; qd22 : XTerm; qm : XMem; qY : W; qn : W; qr : list int }.

Definition xst_ok (A0 B0 : Z) (s : XSt) : Prop :=
  fits (qB s) = true /\ (phi (qz s) = 6 \/ phi (qz s) = 22) /\ xmem_ok (qm s) /\ xterm_sem 6 (qd6 s) /\ xterm_sem 22 (qd22 s) /\
  fits (qn s) = true /\
  exists r, cong PM (bval (qr s)) r /\
    (qstat s = 3%uint63 -> Reach A0 B0 (val (qha s)) (val (qha s) + 3) (val (qn s)) r) /\
    (qstat s <> 3%uint63 -> Reach A0 B0 (phi (qz s)) (val (qB s)) (val (qn s)) r).

Definition xset_stat (s : XSt) (k : int) : XSt := mkXS (qz s) (qB s) k (qha s) (qd6 s) (qd22 s) (qm s) (qY s) (qn s) (qr s).
Definition xset_mem (s : XSt) (m : XMem) : XSt := mkXS (qz s) (qB s) (qstat s) (qha s) (qd6 s) (qd22 s) m (qY s) (qn s) (qr s).
(** Move by a stretch of [N] applications with cost [R]; fails safely if the count would not fit. *)
Definition xmove (s : XSt) (z1 : int) (B1 : W) (k : int) (N : W) (R : list int) : XSt :=
  let n1 := add (qn s) N in
  if fits N && fits n1 then mkXS z1 B1 k (qha s) (qd6 s) (qd22 s) (qm s) (qY s) n1 (ladd (qr s) R) else xset_stat s 4.
Definition xhalt (s : XSt) (a : W) (N : W) (R : list int) : XSt :=
  let n1 := add (qn s) N in
  if fits N && fits n1 then mkXS (qz s) (qB s) 3 a (qd6 s) (qd22 s) (qm s) (qY s) n1 (ladd (qr s) R) else xset_stat s 4.

Definition xpost (z0 : int) (B : W) (s : XSt) : Prop :=
  qstat s = 0%uint63 -> qz s = z0 /\ val B <= val (qB s) /\ (val (qB s) - val B) mod 4 = 0.
Lemma xpost_stat z0 B s : (qstat s =? 0)%uint63 = false -> xpost z0 B s.
Proof. intros H X. rewrite X in H. discriminate. Qed.

Lemma xst_stat A0 B0 s k : xst_ok A0 B0 s -> qstat s <> 3%uint63 -> k <> 3%uint63 -> xst_ok A0 B0 (xset_stat s k).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & r & Cr & _ & R) N3 K3. unfold xset_stat.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (ex_intro _ r (conj Cr (conj _ _))))))))); cbn [qstat qz qB qn qha].
  - intros X. contradiction.
  - intros _. exact (R N3).
Qed.
Lemma xst_mem A0 B0 s m : xst_ok A0 B0 s -> xmem_ok m -> xst_ok A0 B0 (xset_mem s m).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & r & Cr & R3 & R) M. unfold xset_mem.
  exact (conj H1 (conj H2 (conj M (conj H4 (conj H5 (conj H6 (ex_intro _ r (conj Cr (conj R3 R))))))))).
Qed.

Lemma xmove_ok A0 B0 s z1 B1 k N R r1 :
  xst_ok A0 B0 s -> qstat s <> 3%uint63 -> k <> 3%uint63 -> fits B1 = true -> (phi z1 = 6 \/ phi z1 = 22) ->
  Reach (phi (qz s)) (val (qB s)) (phi z1) (val B1) (val N) r1 -> cong PM (bval R) r1 ->
  xst_ok A0 B0 (xmove s z1 B1 k N R).
Proof.
  intros Hs N3 K3 F Z Rr Cr. unfold xmove. cbv zeta.
  destruct (fits N && fits (add (qn s) N)) eqn:C; [|apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]].
  apply andb_prop in C. destruct C as [FN Fn].
  destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & r & C0 & _ & R0).
  refine (conj F (conj Z (conj H3 (conj H4 (conj H5 (conj Fn (ex_intro _ (r + r1) (conj _ (conj _ _))))))))); cbn [qstat qz qB qn qr qha].
  - apply lc_add; assumption.
  - intros X. contradiction.
  - intros _. rewrite val_add2 by assumption. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ (R0 N3) Rr).
Qed.
Lemma xhalt_ok A0 B0 s a N R r1 :
  xst_ok A0 B0 s -> qstat s <> 3%uint63 ->
  Reach (phi (qz s)) (val (qB s)) (val a) (val a + 3) (val N) r1 -> cong PM (bval R) r1 ->
  xst_ok A0 B0 (xhalt s a N R).
Proof.
  intros Hs N3 Rr Cr. unfold xhalt. cbv zeta.
  destruct (fits N && fits (add (qn s) N)) eqn:C; [|apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]].
  apply andb_prop in C. destruct C as [FN Fn].
  destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & r & C0 & _ & R0).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj Fn (ex_intro _ (r + r1) (conj _ (conj _ _))))))))); cbn [qstat qz qB qn qr qha].
  - apply lc_add; assumption.
  - intros _. rewrite val_add2 by assumption. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ (R0 N3) Rr).
  - intros X. exfalso. apply X. reflexivity.
Qed.

(** ** The detour store *)
Definition xdet_of (s : XSt) (z : int) : XTerm := if (z =? 6)%uint63 then qd6 s else qd22 s.
Definition xput_det (s : XSt) (z : int) (t : XTerm) : XSt :=
  if (z =? 6)%uint63 then mkXS (qz s) (qB s) (qstat s) (qha s) t (qd22 s) (qm s) (qY s) (qn s) (qr s)
  else mkXS (qz s) (qB s) (qstat s) (qha s) (qd6 s) t (qm s) (qY s) (qn s) (qr s).
Definition xget_det (s : XSt) (z : int) (B1 : W) : XSt * XTerm * option (W * W) :=
  let t := xdet_of s z in
  match det_usable (xt t) B1 with
  | Some ab => (s, t, Some ab)
  | None =>
    let t2 := xwalk Wfuel (xroot z B1) in
    (xput_det s z t2, t2, det_usable (xt t2) B1)
  end.

Lemma z_6 (z : int) : (phi z = 6 \/ phi z = 22) -> ((z =? 6)%uint63 = true /\ phi z = 6) \/ ((z =? 6)%uint63 = false /\ phi z = 22).
Proof.
  intros [E|E].
  - left. split; [|exact E]. assert (X : z = 6%uint63) by (apply to_Z_inj; exact E). rewrite X. reflexivity.
  - right. split; [|exact E]. assert (X : z = 22%uint63) by (apply to_Z_inj; exact E). rewrite X. reflexivity.
Qed.

Lemma xget_det_sound A0 B0 s z B1 s0 d oab : xst_ok A0 B0 s -> (phi z = 6 \/ phi z = 22) -> fits B1 = true ->
  xget_det s z B1 = (s0, d, oab) ->
  xst_ok A0 B0 s0 /\ qz s0 = qz s /\ qB s0 = qB s /\ qY s0 = qY s /\ qstat s0 = qstat s /\ qm s0 = qm s /\ qn s0 = qn s /\ qr s0 = qr s /\
  xterm_sem (phi z) d /\
  forall ad bd, oab = Some (ad, bd) -> tok (xt d) = true /\ val (lbase (tL (xt d))) <= val B1 /\ (val B1 - val (lbase (tL (xt d)))) mod 4 = 0 /\
    eval (tL (xt d)) B1 = Some (ad, bd) /\ val bd < val ad + 3.
Proof.
  intros Hs Hz HB H. unfold xget_det in H. cbv zeta in H.
  assert (Ht : xterm_sem (phi z) (xdet_of s z)).
  { destruct Hs as (_ & _ & _ & H4 & H5 & _). unfold xdet_of. destruct (z_6 z Hz) as [[C E]|[C E]]; rewrite C, E; assumption. }
  destruct (det_usable (xt (xdet_of s z)) B1) as [[a b]|] eqn:U.
  - injection H as <- <- <-.
    refine (conj Hs (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj Ht _))))))))).
    intros ad bd E. injection E as <- <-. exact (det_usable_spec _ _ _ _ _ (proj1 Ht) HB U).
  - pose proof (xwalk_sound Wfuel (phi z) (xroot z B1) (xroot_ok z B1 HB Hz)) as Hw. revert H Hw.
    generalize (xwalk Wfuel (xroot z B1)). intros t2 H Hw. injection H as <- <- <-.
    assert (F : forall X, X = xput_det s z t2 -> qz X = qz s /\ qB X = qB s /\ qY X = qY s /\ qstat X = qstat s /\ qm X = qm s /\ qn X = qn s /\ qr X = qr s /\ qha X = qha s).
    { intros X ->. unfold xput_det. destruct (z =? 6)%uint63; exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))))). }
    destruct (F _ eq_refl) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    assert (Ok : xst_ok A0 B0 (xput_det s z t2)).
    { destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & r & C0 & R3 & R0).
      unfold xput_det. destruct (z_6 z Hz) as [[C E]|[C E]]; rewrite C; rewrite E in Hw.
      - exact (conj H1 (conj H2 (conj H3 (conj Hw (conj H5 (conj H6 (ex_intro _ r (conj C0 (conj R3 R0))))))))).
      - exact (conj H1 (conj H2 (conj H3 (conj H4 (conj Hw (conj H6 (ex_intro _ r (conj C0 (conj R3 R0))))))))). }
    refine (conj Ok (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 (conj Hw _))))))))).
    intros ad bd E. exact (det_usable_spec _ _ _ _ _ (proj1 Hw) HB E).
Qed.

(** ** A stop high in the tree, with its cost *)
Definition tshift (t : XTerm) (d : W) : list int * list int * list int :=
  let dl := lW d in let u := lmul (t2 t) dl in
  (ladd (t0 t) (lmul (ladd (t1 t) u) dl), ladd (t1 t) (ladd u u), t2 t).

Definition rsum (T DD : W) (A1 A2 A3 : list int) : option (list int) :=
  match sums T with
  | Some (s1l, s2l) => let Dl := lW DD in Some (ladd (lmul (lW T) A1) (ladd (lmul Dl (lmul s1l A2)) (lmul (lmul Dl Dl) (lmul s2l A3))))
  | None => None
  end.
Lemma rsum_spec T DD A1 A2 A3 R a1 a2 a3 : fits T = true -> 1 <= val T -> rsum T DD A1 A2 A3 = Some R ->
  cong PM (bval A1) a1 -> cong PM (bval A2) a2 -> cong PM (bval A3) a3 ->
  cong PM (bval R) (val T * a1 + val DD * s1 (Z.to_nat (val T)) * a2 + val DD * val DD * s2 (Z.to_nat (val T)) * a3).
Proof.
  intros F HT H C1 C2 C3. unfold rsum in H. destruct (sums T) as [[s1l s2l]|] eqn:S; [|discriminate]. injection H as <-.
  destruct (sums_spec T s1l s2l F HT S) as [S1 S2]. lcg.
Qed.

Definition xdo_stop (s : XSt) (L : XLv) : XSt :=
  let t := xterm_of L in let tt := xt t in
  let z := qz s in let B := qB s in let Y := qY s in
  let D1 := tD tt in let B1 := add B D1 in let z1 := tna tt in
  let L0 := xl L in let a := la L0 in let b := lb L0 in let g := lg L0 in let thr := lthr L0 in
  if negb (fits B1) || negb (leb (wc 1) D1) then xset_stat s 4 else
  if (z1 =? z)%uint63 && (low2 D1 =? 0)%uint63 then
    match pick B Y D1 (maxq a b g thr D1) with
    | Some (T, yT) =>
      match rsum T D1 (t0 t) (t1 t) (t2 t), mul_nn T (wc (tlen t)) with
      | Some R, Some N => let Bn := add B yT in xmove s z Bn (if eqb Bn Y then 1%uint63 else 0%uint63) N R
      | _, _ => xset_stat s 4
      end
    | None => xmove s z1 B1 2 (wc (tlen t)) (t0 t)
    end
  else
    let '(s0, d, oab) := xget_det s z1 B1 in
    match oab with
    | Some (ad, bd) =>
      let dd := xt d in
      let Dt := add D1 (tD dd) in
      if (tna dd =? z)%uint63 && (low2 Dt =? 0)%uint63 && fits Dt && leb (wc 1) Dt && (tlen t + tlen d <? 1099511627776)%uint63 then
        let q1 := maxq a b g thr Dt in
        let q2 := maxq ad bd (lg (tL dd)) (lthr (tL dd)) Dt in
        match pick B Y Dt (if ltb q1 q2 then q1 else q2) with
        | Some (T, yT) =>
          let '(e0, e1, e2) := tshift d (sub B1 (lbase (tL dd))) in
          match rsum T Dt (ladd (t0 t) e0) (ladd (t1 t) e1) (ladd (t2 t) e2), mul_nn T (wc (tlen t + tlen d)) with
          | Some R, Some N => let Bn := add B yT in xmove s0 z Bn (if eqb Bn Y then 1%uint63 else 0%uint63) N R
          | _, _ => xset_stat s0 4
          end
        | None => xmove s0 z1 B1 2 (wc (tlen t)) (t0 t)
        end
      else xmove s0 z1 B1 2 (wc (tlen t)) (t0 t)
    | None => xmove s0 z1 B1 2 (wc (tlen t)) (t0 t)
    end.

Lemma stat01 Bn Y : (if eqb Bn Y then 1%uint63 else 0%uint63) <> 3%uint63.
Proof. destruct (eqb Bn Y); apply int_ne; reflexivity. Qed.

Lemma xmove_post z0 B s z1 B1 k N R : z1 = z0 -> val B <= val B1 -> (val B1 - val B) mod 4 = 0 -> qz s = z0 -> qB s = B ->
  xpost z0 B (xmove s z1 B1 k N R).
Proof.
  intros Z L M E1 E2 X. unfold xmove in *. cbv zeta in *.
  destruct (fits N && fits (add (qn s) N)); cbn [qz qB qstat xset_stat] in *.
  - split; [exact Z|]. split; assumption.
  - rewrite E1, E2. split; [reflexivity|]. split; [lia|]. rewrite Z.sub_diag. reflexivity.
Qed.
Lemma xpost_of z0 B s1 : (qstat s1 =? 0)%uint63 = false \/ (qz s1 = z0 /\ val B <= val (qB s1) /\ (val (qB s1) - val B) mod 4 = 0) -> xpost z0 B s1.
Proof. intros [H|H] X; [rewrite X in H; discriminate|exact H]. Qed.

Lemma xpost_fail z0 B s k : (k =? 0)%uint63 = false -> xpost z0 B (xset_stat s k).
Proof. intros K X. cbn [qstat xset_stat] in X. rewrite X in K. discriminate. Qed.
Lemma xpost_move_hop z0 B s z1 B1 N R : xpost z0 B (xmove s z1 B1 2 N R).
Proof. unfold xmove. cbv zeta. destruct (fits N && fits (add (qn s) N)); apply xpost_stat; reflexivity. Qed.

Lemma xdo_stop_sound A0 B0 s L :
  xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xlv_ok (phi (qz s)) L -> lbase (xl L) = qB s ->
  val (lthr (xl L)) <= val (la (xl L)) -> val (lb (xl L)) < val (la (xl L)) + 3 -> val (lb (xl L)) mod 2 = 0 ->
  fits (add (lc (xl L)) (wc 7)) = true -> fits (sub (lc (xl L)) (wc 2)) = true -> phi (xlen L) + 1 < 1099511627776 ->
  xst_ok A0 B0 (xdo_stop s L) /\ xpost (qz s) (qB s) (xdo_stop s L).
Proof.
  intros Hs N3 HL HbL Hta Hlt Hev F7 F2 Hn. unfold xdo_stop. cbv zeta.
  pose proof (xterm_of_ok _ L HL Hev F7 F2 Hn) as [Ht Htc].
  specialize (Htc eq_refl). destruct Htc as (Hlen & P0 & P1 & P2 & Cp0 & Cp1 & Cp2 & Rt).
  change (tL (xt (xterm_of L))) with (xl L) in Rt.
  destruct (Ht eq_refl) as (_ & Hz1 & FD & _). change (tL (xt (xterm_of L))) with (xl L) in Ht.
  pose proof Hs as (SB & Sz & Sm & S6 & S22 & Sn & _).
  pose proof HL as (HF & Hg & Hth & Hsum & _).
  generalize HF; intros HF'.
  unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' Fc]. apply andb_prop in HF'. destruct HF' as [HF' Fth]. apply andb_prop in HF'. destruct HF' as [HF' Fbs]. apply andb_prop in HF'. destruct HF' as [HF' Fg]. apply andb_prop in HF'. destruct HF' as [Fa Fb].
  set (t := xterm_of L) in *. set (D1 := tD (xt t)) in *. set (z1 := tna (xt t)) in *.
  destruct (negb (fits (add (qB s) D1)) || negb (leb (wc 1) D1)) eqn:G0.
  { split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]. }
  apply orb_false_iff in G0. destruct G0 as [G0 G1]. apply negb_false_iff in G0, G1. apply leb_spec_W in G1. rewrite val_wc in G1. change (phi 1%uint63) with 1 in G1.
  assert (VB1 : val (add (qB s) D1) = val (qB s) + val D1) by (apply val_add2; assumption).
  (** the single word *)
  assert (Word : Reach (phi (qz s)) (val (qB s)) (phi z1) (val (add (qB s) D1)) (phi (tlen t)) P0).
  { pose proof (Rt 0 ltac:(lia) ltac:(reflexivity)) as X. rewrite !Z.mul_0_r, !Z.sub_0_r, !Z.add_0_r in X.
    rewrite HbL in X. rewrite VB1. eapply Rconv4; [apply X; [exact Hta|exact Hlt]|reflexivity|reflexivity|reflexivity|ring]. }
  assert (Hop : forall s0, xst_ok A0 B0 s0 -> qz s0 = qz s -> qB s0 = qB s -> qstat s0 <> 3%uint63 ->
     xst_ok A0 B0 (xmove s0 z1 (add (qB s) D1) 2 (wc (tlen t)) (t0 t)) /\ xpost (qz s) (qB s) (xmove s0 z1 (add (qB s) D1) 2 (wc (tlen t)) (t0 t))).
  { intros s0 H0 E1 E2 E3. split; [|apply xpost_move_hop].
    apply (xmove_ok _ _ _ _ _ _ _ _ P0 H0 E3); [apply int_ne; reflexivity|exact G0|exact Hz1| |exact Cp0].
    rewrite E1, E2, val_wc. exact Word. }
  destruct ((z1 =? qz s)%uint63 && (low2 D1 =? 0)%uint63) eqn:Dir.
  - apply andb_prop in Dir. destruct Dir as [Ez Em]. apply eqb_true in Ez, Em. rewrite low2_mod in Em. change (phi 0%uint63) with 0 in Em.
    pose proof (maxq_ok (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) D1) as [Fq Hq].
    destruct (pick (qB s) (qY s) D1 (maxq (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) D1)) as [[T yT]|] eqn:Pk; [|apply Hop; [exact Hs|reflexivity|reflexivity|exact N3]].
    destruct (pick_spec _ _ _ _ _ _ Fq Hq Pk) as (FT & Fy & FBn & Ey & BT).
    destruct (rsum T D1 (t0 t) (t1 t) (t2 t)) as [R|] eqn:Rs; [|split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]].
    destruct (mul_nn T (wc (tlen t))) as [N|] eqn:MN; [|split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]].
    destruct (mul_nn_spec _ _ _ MN) as [EN _]. rewrite val_wc in EN.
    pose proof (rsum_spec T D1 _ _ _ R P0 P1 P2 FT ltac:(clear - BT; lia) Rs Cp0 Cp1 Cp2) as CR.
    destruct (add_rounds (qB s) yT D1 T FBn SB Fy Ey) as (V1 & V2 & V3).
    assert (RR : Reach (phi (qz s)) (val (qB s)) (phi (qz s)) (val (qB s) + val T * val D1) (val T * phi (tlen t))
                  (val T * P0 + val D1 * s1 (Z.to_nat (val T)) * P1 + val D1 * val D1 * s2 (Z.to_nat (val T)) * P2)).
    { apply xrounds; [clear - BT; lia|]. intros k Hk.
      assert (Kq : 0 <= k <= val (maxq (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) D1)) by (clear - Hk BT; lia).
      destruct (maxq_spec (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) D1 k Fa Fb Fg Fth Hg ltac:(clear - G1; lia) Hta Hlt Kq) as [Q1 Q2].
      destruct (mod0_ex _ Em) as [j Ej].
      assert (Bk : 0 <= k * val D1) by (apply Z.mul_nonneg_nonneg; lia).
      assert (M : (k * val D1) mod 4 = 0) by (rewrite Ej; replace (k * (4 * j)) with (4 * (k * j)) by ring; apply ex_mod0).
      pose proof (Rt (k * val D1) Bk M Q1 Q2) as X. rewrite HbL, Ez in X.
      eapply Rconv4; [exact X|reflexivity|ring|reflexivity|ring]. }
    split.
    + apply (xmove_ok _ _ _ _ _ _ _ _ (val T * P0 + val D1 * s1 (Z.to_nat (val T)) * P1 + val D1 * val D1 * s2 (Z.to_nat (val T)) * P2) Hs N3 (stat01 _ _) FBn Sz); [|exact CR].
      rewrite V1, EN. exact RR.
    + apply xmove_post; [reflexivity|apply V2; clear - G1 BT; lia|apply V3; exact Em|reflexivity|reflexivity].
  - destruct (xget_det s z1 (add (qB s) D1)) as [[s0 d] oab] eqn:Gd.
    destruct (xget_det_sound _ _ _ _ _ _ _ _ Hs Hz1 G0 Gd) as (H0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hd & Hab).
    assert (N3' : qstat s0 <> 3%uint63) by (rewrite E4; exact N3).
    assert (Fail : xst_ok A0 B0 (xset_stat s0 4) /\ xpost (qz s) (qB s) (xset_stat s0 4)).
    { split; [apply xst_stat; [exact H0|exact N3'|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]. }
    destruct oab as [[ad bd]|]; [|apply Hop; [exact H0|exact E1|exact E2|exact N3']].
    destruct (Hab ad bd eq_refl) as (Td & Bl & Bm & Ed & Lt). clear Hab.
    destruct Hd as [Hds Hdc]. destruct (Hds Td) as (HLd & Zd & FDd & _). specialize (Hdc Td).
    destruct Hdc as (Hlend & Q0 & Q1 & Q2 & Cq0 & Cq1 & Cq2 & Rd).
    destruct ((tna (xt d) =? qz s)%uint63 && (low2 (add D1 (tD (xt d))) =? 0)%uint63 && fits (add D1 (tD (xt d))) && leb (wc 1) (add D1 (tD (xt d)))
              && (tlen t + tlen d <? 1099511627776)%uint63) eqn:C; [|apply Hop; [exact H0|exact E1|exact E2|exact N3']].
    apply andb_prop in C. destruct C as [C Clen]. apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C FDt]. apply andb_prop in C. destruct C as [Ezd Em].
    apply eqb_true in Ezd, Em. rewrite low2_mod in Em. change (phi 0%uint63) with 0 in Em.
    apply leb_spec_W in C4. rewrite val_wc in C4. change (phi 1%uint63) with 1 in C4. apply ltb_true in Clen. change (phi 1099511627776%uint63) with 1099511627776 in Clen.
    assert (Elen : phi (tlen t + tlen d)%uint63 = phi (tlen t) + phi (tlen d)) by (apply phi_of_cg; [apply cg_add; apply cg_refl|clear - Hlen Hlend; lia]).
    assert (VDt : val (add D1 (tD (xt d))) = val D1 + val (tD (xt d))) by (apply val_add2; assumption).
    pose proof HLd as [HFd [Hgd [Hthd [_ _]]]].
    generalize HFd; intros HF'.
    unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Ftd]. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Fgd]. apply andb_prop in HF'. destruct HF' as [_ _].
    destruct (eval_spec _ _ _ _ HFd Hgd G0 Ed) as (Fad & Fbd & Vad & Vbd & Vtd).
    set (Dt := add D1 (tD (xt d))) in *.
    pose proof (maxq_ok (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) Dt) as [Fq1 Hq1].
    pose proof (maxq_ok ad bd (lg (tL (xt d))) (lthr (tL (xt d))) Dt) as [Fq2 Hq2].
    set (q1 := maxq (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) Dt) in *.
    set (q2 := maxq ad bd (lg (tL (xt d))) (lthr (tL (xt d))) Dt) in *.
    assert (Qm : fits (if ltb q1 q2 then q1 else q2) = true /\ 0 <= val (if ltb q1 q2 then q1 else q2) /\ val (if ltb q1 q2 then q1 else q2) <= val q1 /\ val (if ltb q1 q2 then q1 else q2) <= val q2).
    { destruct (ltb q1 q2) eqn:Lq.
      - apply ltb_spec_W in Lq. split; [exact Fq1|]. clear - Hq1 Lq. lia.
      - apply ltb_false_W in Lq. split; [exact Fq2|]. clear - Hq2 Lq. lia. }
    destruct Qm as (Fqm & Hqm & Qm1 & Qm2).
    destruct (pick (qB s) (qY s) Dt (if ltb q1 q2 then q1 else q2)) as [[T yT]|] eqn:Pk; [|apply Hop; [exact H0|exact E1|exact E2|exact N3']].
    destruct (pick_spec _ _ _ _ _ _ Fqm Hqm Pk) as (FT & Fy & FBn & Ey & BT).
    set (yd := val (add (qB s) D1) - val (lbase (tL (xt d)))).
    assert (Vyd : val (sub (add (qB s) D1) (lbase (tL (xt d)))) = yd).
    { pose proof (lv_bounds _ HFd) as (_ & _ & _ & B4 & _ & _). pose proof (fits_spec _ G0). apply val_sub. lia. }
    unfold tshift. cbv beta iota zeta.
    lazymatch goal with |- context [match rsum ?T0 ?D0 ?a0 ?b0 ?c0 with _ => _ end] => destruct (rsum T0 D0 a0 b0 c0) as [R|] eqn:Rs end; [|exact Fail].
    destruct (mul_nn T (wc (tlen t + tlen d))) as [N|] eqn:MN; [|exact Fail].
    destruct (mul_nn_spec _ _ _ MN) as [EN _]. rewrite val_wc, Elen in EN.
    set (A1 := P0 + (Q0 + Q1 * yd + Q2 * (yd * yd))). set (A2 := P1 + (Q1 + 2 * Q2 * yd)). set (A3 := P2 + Q2).
    pose proof (rsum_spec T Dt _ _ _ R A1 A2 A3 FT ltac:(clear - BT; lia) Rs) as CR.
    assert (CR' : cong PM (bval R) (val T * A1 + val Dt * s1 (Z.to_nat (val T)) * A2 + val Dt * val Dt * s2 (Z.to_nat (val T)) * A3)).
    { apply CR.
      - unfold A1. eapply cong_eq. 
        + lcg_build.
        + rewrite ?Vyd. ring.
      - unfold A2. eapply cong_eq.
        + lcg_build.
        + rewrite ?Vyd. ring.
      - unfold A3. eapply cong_eq.
        + lcg_build.
        + ring. }
    clear CR.
    destruct (add_rounds (qB s) yT Dt T FBn SB Fy Ey) as (V1 & V2 & V3).
    assert (RR : Reach (phi (qz s)) (val (qB s)) (phi (qz s)) (val (qB s) + val T * val Dt) (val T * (phi (tlen t) + phi (tlen d)))
                  (val T * A1 + val Dt * s1 (Z.to_nat (val T)) * A2 + val Dt * val Dt * s2 (Z.to_nat (val T)) * A3)).
    { apply xrounds; [clear - BT; lia|]. intros k Hk. set (K := k * val Dt).
      destruct (mod0_ex _ Em) as [j Ej]. destruct (mod0_ex _ Bm) as [i Ei].
      assert (Bk : 0 <= K) by (unfold K; apply Z.mul_nonneg_nonneg; clear - Hk C4; lia).
      assert (M : K mod 4 = 0) by (unfold K; rewrite Ej; replace (k * (4 * j)) with (4 * (k * j)) by ring; apply ex_mod0).
      assert (M2 : (yd + K) mod 4 = 0) by (unfold yd; rewrite Ei; destruct (mod0_ex _ M) as [l El]; rewrite El; replace (4 * i + 4 * l) with (4 * (i + l)) by ring; apply ex_mod0).
      assert (Kq1 : 0 <= k <= val q1) by (clear - Hk BT Qm1; lia).
      destruct (maxq_spec (la (xl L)) (lb (xl L)) (lg (xl L)) (lthr (xl L)) Dt k Fa Fb Fg Fth Hg ltac:(clear - C4; lia) Hta Hlt Kq1) as [T1 T2].
      assert (Kq2 : 0 <= k <= val q2) by (clear - Hk BT Qm2; lia).
      destruct (maxq_spec ad bd (lg (tL (xt d))) (lthr (tL (xt d))) Dt k Fad Fbd Fgd Ftd Hgd ltac:(clear - C4; lia) Vtd Lt Kq2) as [T3 T4].
      fold K in T1, T2, T3, T4.
      pose proof (Rt K Bk M T1 T2) as X1. rewrite HbL in X1.
      assert (T3' : val (lthr (tL (xt d))) <= val (la (tL (xt d))) - (val (lg (tL (xt d))) - 1) * (yd + K)) by (rewrite Vad in T3; unfold yd; clear - T3; lia).
      assert (T4' : val (lb (tL (xt d))) + val (lg (tL (xt d))) * (yd + K) < val (la (tL (xt d))) - (val (lg (tL (xt d))) - 1) * (yd + K) + 3).
      { rewrite Vad, Vbd in T4. unfold yd. replace (val (la (tL (xt d))) - (val (lg (tL (xt d))) - 1) * (val (add (qB s) D1) - val (lbase (tL (xt d))) + K))
          with (val (la (tL (xt d))) - (val (lg (tL (xt d))) - 1) * (val (add (qB s) D1) - val (lbase (tL (xt d)))) - (val (lg (tL (xt d))) - 1) * K) by ring.
        replace (val (lb (tL (xt d))) + val (lg (tL (xt d))) * (val (add (qB s) D1) - val (lbase (tL (xt d))) + K))
          with (val (lb (tL (xt d))) + val (lg (tL (xt d))) * (val (add (qB s) D1) - val (lbase (tL (xt d)))) + val (lg (tL (xt d))) * K) by ring. exact T4. }
      pose proof (Rd (yd + K) ltac:(unfold yd; clear - Bl Bk; lia) M2 T3' T4') as X2. rewrite Ezd in X2.
      assert (P2s : val (lbase (tL (xt d))) + (yd + K) = val (qB s) + K + val D1) by (unfold yd; rewrite VB1; ring).
      rewrite P2s in X2.
      pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ X1 X2) as X3.
      assert (Eb : val (qB s) + K + val D1 + val (tD (xt d)) = val (qB s) + (k + 1) * val Dt) by (unfold K; rewrite VDt; clear; lia).
      assert (Er : P0 + P1 * K + P2 * (K * K) + (Q0 + Q1 * (yd + K) + Q2 * ((yd + K) * (yd + K))) = A1 + A2 * (k * val Dt) + A3 * (k * val Dt * (k * val Dt))).
      { unfold A1, A2, A3, K. generalize yd (val Dt). intros. ring. }
      eapply Rconv4; [exact X3|reflexivity|exact Eb|clear; lia|exact Er]. }
    split.
    + apply (xmove_ok _ _ _ _ _ _ _ _ (val T * A1 + val Dt * s1 (Z.to_nat (val T)) * A2 + val Dt * val Dt * s2 (Z.to_nat (val T)) * A3) H0 N3' (stat01 _ _) FBn Sz); [|exact CR'].
      rewrite E1, E2, V1, EN. exact RR.
    + apply xmove_post; [reflexivity|apply V2; clear - C4 BT; lia|apply V3; exact Em|exact E1|exact E2].
Qed.

(** ** Costs of a block, modulo 2^315 *)
Definition s4 (h : int) : W := mkW (if (h <? 4611686018427387904)%uint63 then 0%uint63 else ones) h.
Lemma s4_val h : val (s4 h) = sg h.
Proof.
  unfold s4, val. cbn [hi lo]. destruct (h <? 4611686018427387904)%uint63 eqn:C.
  - apply ltb_true in C. change (phi 4611686018427387904%uint63) with P62 in C. replace (sg 0%uint63) with 0 by reflexivity.
    unfold sg. destruct (phi h <? P62) eqn:D; [lia|apply Z.ltb_ge in D; lia].
  - apply ltb_false in C. change (phi 4611686018427387904%uint63) with P62 in C. replace (sg ones) with (-1) by reflexivity.
    unfold sg. destruct (phi h <? P62) eqn:D; [apply Z.ltb_lt in D; lia|lia].
Qed.
Definition LPA : list int := [2147483648%uint63].
Definition LPB : list int := [4611686018427387904%uint63].
Definition LPC : list int := [0%uint63; 1073741824%uint63].
Definition LPD : list int := [0%uint63; 2305843009213693952%uint63].
Lemma lc_PA : cong PM (bval LPA) PA. Proof. exists 0. reflexivity. Qed.
Lemma lc_PB : cong PM (bval LPB) PB. Proof. exists 0. reflexivity. Qed.
Lemma lc_PC : cong PM (bval LPC) PC. Proof. exists 0. reflexivity. Qed.
Lemma lc_PD : cong PM (bval LPD) PD. Proof. exists 0. reflexivity. Qed.

Definition l5 (x : P5) : list int :=
  ladd (lW (wc (q0 x))) (ladd (lmul (lW (wc (q1 x))) LPA) (ladd (lmul (lW (wc (q2 x))) LPB) (ladd (lmul (lW (wc (q3 x))) LPC) (lmul (lW (s4 (q4 x))) LPD)))).
Lemma l5_spec x : cong PM (bval (l5 x)) (val5 x).
Proof.
  unfold l5. eapply cong_eq.
  - apply lc_add; [apply lc_W|]. apply lc_add; [apply lc_mul; [apply lc_W|apply lc_PA]|]. apply lc_add; [apply lc_mul; [apply lc_W|apply lc_PB]|].
    apply lc_add; [apply lc_mul; [apply lc_W|apply lc_PC]|]. apply lc_mul; [apply lc_W|apply lc_PD].
  - rewrite !val_wc, s4_val. unfold val5. ring.
Qed.


Definition lpval (p : Poly) (b S g : W) : list int :=
  let lb_ := lW b in let lS := lW S in let lg_ := lW g in
  ladd (lmul (l5 (pA p)) (lmul lb_ lb_)) (ladd (lmul (l5 (pB p)) (lmul lb_ lS)) (ladd (lmul (l5 (pC p)) (lmul lb_ lg_)) (ladd (lmul (l5 (pD p)) (lmul lS lS))
  (ladd (lmul (l5 (pE p)) (lmul lS lg_)) (ladd (lmul (l5 (pF p)) (lmul lg_ lg_)) (ladd (lmul (l5 (pG p)) lb_) (ladd (lmul (l5 (pH p)) lS) (ladd (lmul (l5 (pI p)) lg_) (l5 (pJ p)))))))))).
Ltac lcg_build ::= repeat match goal with
  | |- cong PM (bval (ladd _ _)) _ => eapply lc_add
  | |- cong PM (bval (lmul _ _)) _ => eapply lc_mul
  | |- cong PM (bval (lW _)) _ => apply lc_W
  | |- cong PM (bval (lz _)) _ => apply lc_z
  | |- cong PM (bval (lzi ?n ?k)) _ => let v := eval vm_compute in (if n then - phi k else phi k) in apply (lc_zi n k v); [vm_compute; reflexivity|vm_compute; reflexivity]
  | |- cong PM (bval (if _ then _ else _)) _ => eapply lc_if
  | |- cong PM (bval LINV3) _ => apply lc_INV3
  | |- cong PM (bval (l5 _)) _ => apply l5_spec
  | |- cong PM (bval []) _ => apply (cong_refl PM 0)
  | H : cong PM (bval ?x) _ |- cong PM (bval ?x) _ => exact H
  end.

Lemma lpval_spec p b S g : cong PM (bval (lpval p b S g)) (pval p (val b) (val S) (val g)).
Proof.
  pose proof (l5_spec (pA p)). pose proof (l5_spec (pB p)). pose proof (l5_spec (pC p)). pose proof (l5_spec (pD p)). pose proof (l5_spec (pE p)).
  pose proof (l5_spec (pF p)). pose proof (l5_spec (pG p)). pose proof (l5_spec (pH p)). pose proof (l5_spec (pI p)). pose proof (l5_spec (pJ p)).
  unfold lpval. cbv zeta. eapply cong_eq; [lcg_build|]. unfold pval. ring.
Qed.
Ltac lcg_build ::= repeat match goal with
  | |- cong PM (bval (ladd _ _)) _ => eapply lc_add
  | |- cong PM (bval (lmul _ _)) _ => eapply lc_mul
  | |- cong PM (bval (lW _)) _ => apply lc_W
  | |- cong PM (bval (lz _)) _ => apply lc_z
  | |- cong PM (bval (lzi ?n ?k)) _ => let v := eval vm_compute in (if n then - phi k else phi k) in apply (lc_zi n k v); [vm_compute; reflexivity|vm_compute; reflexivity]
  | |- cong PM (bval (if _ then _ else _)) _ => eapply lc_if
  | |- cong PM (bval LINV3) _ => apply lc_INV3
  | |- cong PM (bval (l5 _)) _ => apply l5_spec
  | |- cong PM (bval (lpval _ _ _ _)) _ => apply lpval_spec
  | |- cong PM (bval []) _ => apply (cong_refl PM 0)
  | H : cong PM (bval ?x) _ |- cong PM (bval ?x) _ => exact H
  end.


(** The detour term for a block, and what it gives. *)
Definition xenv_of (s : XSt) : Env * XTerm :=
  let z := qz s in
  let t := if (z =? 22)%uint63 then qd6 s else qd22 s in
  if tok (xt t) && (tna (xt t) =? z)%uint63 && leb (lbase (tL (xt t))) (qB s) && (hi (tD (xt t)) =? 0)%uint63 then (mkEnv z true (lo (tD (xt t))), t)
  else (mkEnv z false 0%uint63, t).

Lemma xenv_of_spec A0 B0 s v t : xst_ok A0 B0 s -> xenv_of s = (v, t) ->
  vz v = qz s /\ xterm_sem (28 - phi (qz s)) t /\
  (vhas v = true -> tok (xt t) = true /\ phi (tna (xt t)) = phi (qz s) /\ val (lbase (tL (xt t))) <= val (qB s) /\ val (tD (xt t)) = phi (vd2 v)).
Proof.
  intros (_ & Sz & _ & S5 & S6 & _) H. unfold xenv_of in H. cbv zeta in H.
  assert (Ht : xterm_sem (28 - phi (qz s)) (if (qz s =? 22)%uint63 then qd6 s else qd22 s)).
  { destruct (z_cases _ Sz) as [[C E]|[C E]]; rewrite C, E; [exact S5|exact S6]. }
  destruct (tok _ && _ && _ && _) eqn:C in H.
  - injection H as <- <-. split; [reflexivity|]. split; [exact Ht|]. intros _.
    apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
    apply eqb_true in C2. apply leb_spec_W in C3. apply Uint63.eqb_spec in C4.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. apply val_hi0. exact C4.
  - injection H as <- <-. split; [reflexivity|]. split; [exact Ht|]. intros X. discriminate X.
Qed.

Lemma x_det_hyp z t B d2 dl dres By ad bd :
  xterm_sem (28 - z) t -> tok (xt t) = true -> phi (tna (xt t)) = z -> val (lbase (tL (xt t))) <= val B -> val (tD (xt t)) = d2 ->
  (val B - val (lbase (tL (xt t))) + dres) mod 4 = 0 -> 0 <= dl -> val By = val B + dl -> fits By = true ->
  eval (tL (xt t)) By = Some (ad, bd) -> val bd < val ad + 3 -> fits B = true ->
  let '(e0, e1, e2) := tshift t (sub B (lbase (tL (xt t)))) in
  exists D0 D1 D2, cong PM (bval e0) D0 /\ cong PM (bval e1) D1 /\ cong PM (bval e2) D2 /\ XDet (28 - z) z (val B) d2 dl dres (phi (tlen t)) D0 D1 D2.
Proof.
  intros [Hs Hc] Tt Hz Hb Hd Hm Dl VBy FBy He Lt FB.
  destruct (Hs Tt) as ([HF [Hg [_ [_ _]]]] & _ & _ & _).
  destruct (Hc Tt) as (_ & Q0 & Q1 & Q2 & C0 & C1 & C2 & R).
  destruct (eval_spec _ _ _ _ HF Hg FBy He) as (_ & _ & Va & Vb & Vt).
  assert (Vd : val (sub B (lbase (tL (xt t)))) = val B - val (lbase (tL (xt t)))).
  { pose proof (lv_bounds _ HF) as (_ & _ & _ & B4 & _ & _). apply fits_spec in FB. apply val_sub. lia. }
  unfold tshift. cbv zeta. set (dd := val B - val (lbase (tL (xt t)))) in *.
  exists (Q0 + Q1 * dd + Q2 * (dd * dd)), (Q1 + 2 * Q2 * dd), Q2.
  split; [eapply cong_eq; [lcg_build|]; rewrite Vd; ring|]. split; [eapply cong_eq; [lcg_build|]; rewrite Vd; ring|]. split; [exact C2|].
  intros y Hy Hyr.
  set (y1 := dd + y).
  set (ym := val By - val (lbase (tL (xt t)))) in *.
  assert (Y0 : 0 <= y1) by (unfold y1, dd; clear - Hb Hy; lia).
  assert (Ylt : y1 <= ym) by (unfold y1, ym, dd; clear - Hy VBy; lia).
  assert (M : y1 mod 4 = 0) by (unfold y1; exact (mod_comb _ _ _ Hm Hyr)).
  assert (P1 : (val (lg (tL (xt t))) - 1) * y1 <= (val (lg (tL (xt t))) - 1) * ym) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|exact Ylt]).
  assert (P2 : val (lg (tL (xt t))) * y1 <= val (lg (tL (xt t))) * ym) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|exact Ylt]).
  pose proof (R y1 Y0 M ltac:(clear - P1 Va Vt; lia) ltac:(clear - P1 P2 Va Vb Lt; lia)) as X.
  rewrite Hz, Hd in X.
  assert (E1 : val (lbase (tL (xt t))) + y1 = val B + y) by (unfold y1, dd; ring).
  rewrite E1 in X.
  eapply Rconv4; [exact X|reflexivity|reflexivity|reflexivity|unfold y1; generalize dd; intros; ring].
Qed.

(** One application of a block lemma with its count and cost. *)
Lemma x_apply_ent z c e len2 D0 D1 DC :
  xlv_ok z c -> x_ok e -> phi (ez (xs e)) = z -> phi (ec (xs e)) = val (lc (xl c)) -> phi (era (xs e)) = val (la (xl c)) mod 4 -> phi (erb (xs e)) = val (lb (xl c)) mod 4 ->
  phi (eGm (xs e)) <= val (lg (xl c)) -> reg (xs e) (val (lb (xl c))) (val (la (xl c)) + val (lb (xl c))) (val (lg (xl c))) ->
  val (lthr (xl c)) + (val (lg (xl c)) - 1) * phi (elast (xs e)) <= val (la (xl c)) ->
  (edet (xs e) = true -> XDet (28 - z) z (val (lbase (xl c))) (phi (ed2 (xs e))) (phi (edlast (xs e))) (phi (edres (xs e))) len2 D0 D1 DC) ->
  exists P0 P1 P2, cong PM (bval (c0 c)) P0 /\ cong PM (bval (c1 c)) P1 /\ cong PM (bval (c2 c)) P2 /\
    Reach z (val (lbase (xl c))) z (val (lbase (xl c)) + phi (eY (xs e))) (totn (xk e) (phi (xlen c)) len2)
      (totr (xk e) P0 P1 P2 D0 D1 DC (val (lb (xl c))) (val (la (xl c)) + val (lb (xl c))) (val (lg (xl c)))).
Proof.
  intros (_ & Hg & Hth & Hs & _ & P0 & P1 & P2 & C0 & C1 & C2 & HR) (_ & _ & Hsem) Hz Hc Hra Hrb Hgm Hreg Hth2 Hdet.
  exists P0, P1, P2. split; [exact C0|]. split; [exact C1|]. split; [exact C2|].
  pose proof (Hsem (val (lbase (xl c))) (val (la (xl c))) (val (lb (xl c))) (val (lg (xl c))) (phi (xlen c)) P0 P1 P2 len2 D0 D1 DC) as X.
  rewrite Hz in X. apply X; try assumption.
  - rewrite Hs, Hc. reflexivity.
  - symmetry. exact Hra.
  - symmetry. exact Hrb.
  - intros y Hy Hm. apply HR; [clear - Hy; lia|exact Hm|].
    assert (P : (val (lg (xl c)) - 1) * y <= (val (lg (xl c)) - 1) * phi (elast (xs e))) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|apply Hy]).
    clear - P Hth2. lia.
Qed.

Definition xtry_block (xc0 : XLv) (s : XSt) : XMem * option XSt :=
  let c := xl xc0 in
  let B := qB s in let b := lb c in let a := la c in let g := lg c in let m := qm s in
  if negb (leb (wc 281474976710656) g) || negb (eqb (lbase c) B) || negb (((low2 b) land 1 =? 1)%uint63)
     || negb ((hi (lc c) =? 0)%uint63) then (m, None) else
  let S := add a b in
  if negb (leb (wc 0) b) || negb (leb S (mkW 8589934592 0)) || negb (leb (wc 0) S) || negb (leb b S) || negb (leb (wc 1) g) || negb (lv_fits c) || negb (xlen xc0 <? 1099511627776)%uint63 then (m, None) else
  let w := fxdiv S g in let bt := fxdiv b g in
  if (288230376151711744 <=? w)%uint63 || (w <? 1099511627776)%uint63 || (bt <? 64)%uint63 || (1152921504606846976 <=? bt)%uint63 then (m, None) else
  let wl := (w - 2)%uint63 in let wh := (w + 2)%uint63 in let bl := (bt - 2)%uint63 in let bh := (bt + 2)%uint63 in
  let S28 := mulk 268435456 S in let b28 := mulk 268435456 b in
  match mul_nn (wc wl) g, mul_nn (wc wh) g, mul_nn (wc bl) g, mul_nn (wc bh) g with
  | Some p1, Some p2, Some p3, Some p4 =>
    if leb p1 S28 && leb S28 p2 && leb p3 b28 && leb b28 p4 then
      let '(v, t) := xenv_of s in
      let x := mkCtx (lo (lc c)) (low2 a) (low2 b) in
      let '(m1, oe) := xbn bfuel m v x bt w in
      match oe with
      | None => (m1, None)
      | Some xe =>
        let e := xs xe in let k := xk xe in
        let last := wc (elast e) in
        let Bn := add B (wc (eY e)) in
        if keyok v x e && negb (eY e =? 0)%uint63 && reg_exact e bl bh wl wh && leb (wc (eGm e)) g && fits Bn && leb Bn (qY s) && fits (add B (wc (edlast e))) then
          match mul_nn (sub g (wc 1)) last with
          | Some h =>
            if leb (add (lthr c) h) a && fits h && fits (add (lthr c) h) then
              let dok := negb (edet e) ||
                 (vhas v && (low2 (add (sub B (lbase (tL (xt t)))) (wc (edres e))) =? 0)%uint63 &&
                  match eval (tL (xt t)) (add B (wc (edlast e))) with
                  | Some (ad, bd) => ltb bd (add ad (wc 3))
                  | None => false
                  end) in
              if dok then
                let '(e0, e1, e2) := if edet e then tshift t (sub B (lbase (tL (xt t)))) else ([], [], []) in
                let len2 := if edet e then tlen t else 0%uint63 in
                let N := add (add (mulk (en k) (wc (xlen xc0))) (wc (eapps k))) (mulk (end_ k) (wc len2)) in
                let R := ladd (lmul (c0 xc0) (lW (wc (en k)))) (ladd (lmul (c1 xc0) (lW (wc (em1 k)))) (ladd (lmul (c2 xc0) (l5 (em2 k)))
                          (ladd (lpval (ep k) b S g) (ladd (lmul e0 (lW (wc (end_ k)))) (ladd (lmul e1 (lW (wc (emd1 k)))) (lmul e2 (l5 (emd2 k)))))))) in
                (m1, Some (xmove (xset_mem s m1) (qz s) Bn (if eqb Bn (qY s) then 1%uint63 else 0%uint63) N R))
              else (m1, None)
            else (m1, None)
          | None => (m1, None)
          end
        else (m1, None)
      end
    else (m, None)
  | _, _, _, _ => (m, None)
  end.



Lemma xblock_finish A0 B0 s c xe m1 (E0 E1 E2 : list int) (len2 : int) D0 D1 DC :
  xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xmem_ok m1 -> xlv_ok (phi (qz s)) c -> lbase (xl c) = qB s -> x_ok xe ->
  phi (ez (xs xe)) = phi (qz s) -> phi (ec (xs xe)) = val (lc (xl c)) -> phi (era (xs xe)) = val (la (xl c)) mod 4 -> phi (erb (xs xe)) = val (lb (xl c)) mod 4 ->
  phi (eGm (xs xe)) <= val (lg (xl c)) -> reg (xs xe) (val (lb (xl c))) (val (la (xl c)) + val (lb (xl c))) (val (lg (xl c))) ->
  val (lthr (xl c)) + (val (lg (xl c)) - 1) * phi (elast (xs xe)) <= val (la (xl c)) ->
  (edet (xs xe) = true -> XDet (28 - phi (qz s)) (phi (qz s)) (val (qB s)) (phi (ed2 (xs xe))) (phi (edlast (xs xe))) (phi (edres (xs xe))) (phi len2) D0 D1 DC) ->
  cong PM (bval E0) D0 -> cong PM (bval E1) D1 -> cong PM (bval E2) DC -> phi len2 < 1099511627776 ->
  fits (add (qB s) (wc (eY (xs xe)))) = true -> (val (add (qB s) (wc (eY (xs xe)))) - val (qB s)) mod 4 = 0 ->
  val (add (qB s) (wc (eY (xs xe)))) = val (qB s) + phi (eY (xs xe)) ->
  let k := xk xe in let Bn := add (qB s) (wc (eY (xs xe))) in
  let N := add (add (mulk (en k) (wc (xlen c))) (wc (eapps k))) (mulk (end_ k) (wc len2)) in
  let R := ladd (lmul (c0 c) (lW (wc (en k)))) (ladd (lmul (c1 c) (lW (wc (em1 k)))) (ladd (lmul (c2 c) (l5 (em2 k)))
            (ladd (lpval (ep k) (lb (xl c)) (add (la (xl c)) (lb (xl c))) (lg (xl c))) (ladd (lmul E0 (lW (wc (end_ k)))) (ladd (lmul E1 (lW (wc (emd1 k)))) (lmul E2 (l5 (emd2 k)))))))) in
  xst_ok A0 B0 (xmove (xset_mem s m1) (qz s) Bn (if eqb Bn (qY s) then 1%uint63 else 0%uint63) N R) /\
  xpost (qz s) (qB s) (xmove (xset_mem s m1) (qz s) Bn (if eqb Bn (qY s) then 1%uint63 else 0%uint63) N R).
Proof.
  intros Hs N3 Hm Hc Eb He Hz Hcc Hra Hrb Hgm Hreg Hth2 Hdet CE0 CE1 CE2 Hl2 FBn MY Vbn. cbv zeta.
  rewrite <- Eb in Hdet.
  destruct (x_apply_ent (phi (qz s)) c xe (phi len2) D0 D1 DC Hc He Hz Hcc Hra Hrb Hgm Hreg Hth2 Hdet) as (P0 & P1 & P2 & C0 & C1 & C2 & RX).
  pose proof Hs as (SB & Sz & _).
  pose proof Hc as (HF & _ & _ & _ & Hlen & _).
  destruct He as (_ & Hcb & _). destruct Hcb as (Bn_ & Bm1 & Bm2 & Bap & Bnd & Bmd1 & Bmd2 & Bp).
  pose proof (lv_bounds _ HF) as (B1 & B2 & _ & _ & _ & _).
  unfold lv_fits in HF. repeat (apply andb_prop in HF; destruct HF as [HF ?]).
  assert (VS : val (add (la (xl c)) (lb (xl c))) = val (la (xl c)) + val (lb (xl c))) by (apply val_add2; assumption).
  pose proof (phi_bd63 (en (xk xe))) as Ben. pose proof (phi_bd63 (eapps (xk xe))) as Bapp. pose proof (phi_bd63 (end_ (xk xe))) as Bend.
  pose proof (phi_bd63 len2) as Bl2. pose proof (phi_bd63 (xlen c)) as Bxl.
  assert (Q1 : 0 <= phi (en (xk xe)) * phi (xlen c) <= 1073741824 * 1099511627776) by (split; [apply Z.mul_nonneg_nonneg|apply Z.mul_le_mono_nonneg]; clear - Ben Bxl Bn_ Hlen; lia).
  assert (Q2 : 0 <= phi (end_ (xk xe)) * phi len2 <= 1073741824 * 1099511627776) by (split; [apply Z.mul_nonneg_nonneg|apply Z.mul_le_mono_nonneg]; clear - Bend Bl2 Bnd Hl2; lia).
  assert (M1 : val (mulk (en (xk xe)) (wc (xlen c))) = phi (en (xk xe)) * phi (xlen c)) by (rewrite val_mulk; rewrite val_wc; [reflexivity|clear - Q1; lia]).
  assert (M2 : val (mulk (end_ (xk xe)) (wc len2)) = phi (end_ (xk xe)) * phi len2) by (rewrite val_mulk; rewrite val_wc; [reflexivity|clear - Q2; lia]).
  assert (VN : val (add (add (mulk (en (xk xe)) (wc (xlen c))) (wc (eapps (xk xe)))) (mulk (end_ (xk xe)) (wc len2))) = totn (xk xe) (phi (xlen c)) (phi len2)).
  { assert (V1 : val (add (mulk (en (xk xe)) (wc (xlen c))) (wc (eapps (xk xe)))) = phi (en (xk xe)) * phi (xlen c) + phi (eapps (xk xe)))
      by (rewrite val_add; rewrite M1, val_wc; [reflexivity|clear - Q1 Bapp; lia]).
    rewrite val_add; rewrite V1, M2; [unfold totn; ring|clear - Q1 Q2 Bapp; lia]. }
  split.
  - apply (xmove_ok _ _ _ _ _ _ _ _ (totr (xk xe) P0 P1 P2 D0 D1 DC (val (lb (xl c))) (val (la (xl c)) + val (lb (xl c))) (val (lg (xl c))))
             (xst_mem _ _ _ _ Hs Hm) N3 (stat01 _ _) FBn Sz).
    + cbn [qz qB xset_mem]. rewrite VN, Vbn, <- Eb. exact RX.
    + eapply cong_eq; [lcg_build|]. rewrite !val_wc, VS. unfold totr. atomize. ring.
  - apply xmove_post; [reflexivity| |exact MY|reflexivity|reflexivity]. rewrite Vbn. pose proof (phi_bd63 (eY (xs xe))) as BY. clear - BY. lia.
Qed.
Lemma xtry_block_sound A0 B0 xc0 s m os :
  xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xlv_ok (phi (qz s)) xc0 -> lbase (xl xc0) = qB s -> xtry_block xc0 s = (m, os) ->
  xmem_ok m /\ forall s1, os = Some s1 -> xst_ok A0 B0 s1 /\ xpost (qz s) (qB s) s1.
Proof.
  intros Hs N3 Hxc Eb H. pose proof Hs as (SB & Sz & Sm & S5 & S6 & Sn & _).
  pose proof Hxc as (HF & Hg & Hth & Hsum & Hlen & _).
  set (c := xl xc0) in *.
  generalize HF; intros HF'. unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' Fc]. apply andb_prop in HF'. destruct HF' as [HF' Fth]. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Fg]. apply andb_prop in HF'. destruct HF' as [Fa Fb].
  unfold xtry_block in H. cbv zeta in H. fold c in H.
  ifb H C1; [no H|].
  apply orb_false_iff in C1. destruct C1 as [C1 C1d]. apply orb_false_iff in C1. destruct C1 as [C1 _]. apply orb_false_iff in C1. destruct C1 as [_ _].
  apply negb_false_iff in C1d. apply Uint63.eqb_spec in C1d.
  assert (VS : val (add (la c) (lb c)) = val (la c) + val (lb c)) by (apply val_add2; assumption).
  set (S := add (la c) (lb c)) in *.
  ifb H C2; [no H|].
  apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 C2d]. apply orb_false_iff in C2. destruct C2 as [C2 C2c]. apply orb_false_iff in C2. destruct C2 as [C2a C2b].
  apply negb_false_iff in C2a, C2b, C2c, C2d. apply leb_spec_W in C2a, C2b, C2c, C2d.
  change (val (wc 0)) with 0 in C2a, C2c.
  assert (E96 : val (mkW 8589934592 0) = 79228162514264337593543950336) by reflexivity. rewrite E96 in C2b. clear E96.
  assert (VS28 : val (mulk 268435456 S) = PP * val S).
  { rewrite val_mulk; change (phi 268435456%uint63) with 268435456; [reflexivity|clear - C2b C2c; lia]. }
  assert (Vb28 : val (mulk 268435456 (lb c)) = PP * val (lb c)).
  { rewrite val_mulk; change (phi 268435456%uint63) with 268435456; [reflexivity|clear - C2a C2b C2d; lia]. }
  generalize (fxdiv S (lg c)) H. intros w H'. clear H. rename H' into H.
  generalize (fxdiv (lb c) (lg c)) H. intros bt H'. clear H. rename H' into H.
  ifb H C3; [no H|].
  apply orb_false_iff in C3. destruct C3 as [C3 C3d]. apply orb_false_iff in C3. destruct C3 as [C3 C3c]. apply orb_false_iff in C3. destruct C3 as [C3a C3b].
  apply leb_false in C3a, C3d. apply ltb_false in C3b, C3c.
  change (phi 288230376151711744%uint63) with 288230376151711744 in C3a.
  change (phi 1099511627776%uint63) with 1099511627776 in C3b.
  change (phi 64%uint63) with 64 in C3c.
  change (phi 1152921504606846976%uint63) with 1152921504606846976 in C3d.
  assert (Ewl : phi (w - 2)%uint63 = phi w - 2) by (apply sub2_val; clear - C3b; lia).
  assert (Ewh : phi (w + 2)%uint63 = phi w + 2) by (apply add2_val; clear - C3a; lia).
  assert (Ebl : phi (bt - 2)%uint63 = phi bt - 2) by (apply sub2_val; clear - C3c; lia).
  assert (Ebh : phi (bt + 2)%uint63 = phi bt + 2) by (apply add2_val; clear - C3d; lia).
  generalize (w - 2)%uint63 (w + 2)%uint63 (bt - 2)%uint63 (bt + 2)%uint63 Ewl Ewh Ebl Ebh H. clear Ewl Ewh Ebl Ebh H. intros wl wh bl bh Ewl Ewh Ebl Ebh H.
  destruct (mul_nn (wc wl) (lg c)) as [p1|] eqn:M1; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc wh) (lg c)) as [p2|] eqn:M2; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc bl) (lg c)) as [p3|] eqn:M3; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc bh) (lg c)) as [p4|] eqn:M4; [|cbv beta iota in H; no H].
  cbv beta iota in H.
  ifb H C4; [|no H].
  destruct (mul_nn_spec _ _ _ M1) as [Ep1 _]. destruct (mul_nn_spec _ _ _ M2) as [Ep2 _]. destruct (mul_nn_spec _ _ _ M3) as [Ep3 _]. destruct (mul_nn_spec _ _ _ M4) as [Ep4 _].
  rewrite val_wc in Ep1, Ep2, Ep3, Ep4. clear M1 M2 M3 M4.
  apply andb_prop in C4. destruct C4 as [C4 C4d]. apply andb_prop in C4. destruct C4 as [C4 C4c]. apply andb_prop in C4. destruct C4 as [C4a C4b].
  apply leb_spec_W in C4a, C4b, C4c, C4d. rewrite VS28, Ep1 in C4a. rewrite VS28, Ep2 in C4b. rewrite Vb28, Ep3 in C4c. rewrite Vb28, Ep4 in C4d. rewrite VS in C4a, C4b.
  clear VS28 Vb28 Ep1 Ep2 Ep3 Ep4.
  destruct (xenv_of s) as [v t] eqn:Ev. cbv beta iota in H.
  destruct (xenv_of_spec _ _ _ _ _ Hs Ev) as (Vz & Ht & Hhas).
  assert (Hzv : phi (vz v) = 6 \/ phi (vz v) = 22) by (rewrite Vz; exact Sz).
  pose proof (xbn_sound bfuel (qm s) v (mkCtx (lo (lc c)) (low2 (la c)) (low2 (lb c))) bt w Hzv Sm) as Rk.
  destruct (xbn bfuel (qm s) v (mkCtx (lo (lc c)) (low2 (la c)) (low2 (lb c))) bt w) as [m1 oe] eqn:Bn. clear Bn.
  destruct Rk as [Mm1 He]. cbn [fst snd] in Mm1, He. cbv beta iota in H.
  destruct oe as [xe|]; [|no H].
  specialize (He xe eq_refl). cbv beta iota in H.
  set (e := xs xe) in *. set (k := xk xe) in *. assert (HeE : ent_ok e) by exact (proj1 He).
  ifb H C5; [|no H].
  destruct (mul_nn (sub (lg c) (wc 1)) (wc (elast e))) as [h|] eqn:M5; [|no H].
  destruct (mul_nn_spec _ _ _ M5) as [Eh _]. clear M5.
  rewrite val_wc in Eh. rewrite val_sub_c in Eh by (exact Fg || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in Eh.
  ifb H C6; [|no H].
  ifb H C7; [|no H].
  remember (if edet e then tshift t (sub (qB s) (lbase (tL (xt t)))) else ([], [], [])) as QQ eqn:EQ in H.
  destruct QQ as [[Q0 Q1] Q2].
  injection H as <- <-. split; [exact Mm1|]. intros s1 E. injection E as <-.
  pose proof HeE as [Hbd _]. pose proof Hbd as (_ & _ & _ & _ & _ & BY & MY & _ & _ & BDL & _).
  apply andb_prop in C5. destruct C5 as [C5 FDL]. apply andb_prop in C5. destruct C5 as [C5 _]. apply andb_prop in C5. destruct C5 as [C5 FBn]. apply andb_prop in C5. destruct C5 as [C5 CGm]. apply andb_prop in C5. destruct C5 as [C5 Creg]. apply andb_prop in C5. destruct C5 as [Ck _].
  unfold keyok in Ck. apply andb_prop in Ck. destruct Ck as [Ck Kd2]. apply andb_prop in Ck. destruct Ck as [Ck Kz]. apply andb_prop in Ck. destruct Ck as [Ck Krb]. apply andb_prop in Ck. destruct Ck as [Kc Kra].
  cbn [xc xra xrb] in Kc, Kra, Krb. apply eqb_true in Kc, Kra, Krb, Kz, Kd2. rewrite low2_mod in Kra, Krb.
  apply leb_spec_W in CGm. rewrite val_wc in CGm.
  apply andb_prop in C6. destruct C6 as [C6 Fth2]. apply andb_prop in C6. destruct C6 as [C6 Fh].
  apply leb_spec_W in C6. rewrite (val_add2 _ _ Fth Fh), Eh in C6.
  assert (Vbn : val (add (qB s) (wc (eY e))) = val (qB s) + phi (eY e)).
  { apply val_add_c; [exact SB|clear - BY; lia]. }
  pose proof (phi_bd63 (eY e)) as BY0.
  assert (MY2 : (val (add (qB s) (wc (eY e))) - val (qB s)) mod 4 = 0).
  { rewrite Vbn. replace (val (qB s) + phi (eY e) - val (qB s)) with (phi (eY e)) by ring. exact MY. }
  assert (Hreg : reg e (val (lb c)) (val (la c) + val (lb c)) (val (lg c))) by (apply (reg_exact_sound e bl bh wl wh); try assumption; clear - C3c C3d Ebl Ebh; lia).
  assert (Ez : phi (ez e) = phi (qz s)) by (rewrite Kz, Vz; reflexivity).
  assert (Ec : phi (ec e) = val (lc c)) by (rewrite Kc; symmetry; apply val_hi0; exact C1d).
  destruct (edet e) eqn:Ed.
  - cbn [negb orb] in C7.
    apply andb_prop in C7. destruct C7 as [C7 C7e]. apply andb_prop in C7. destruct C7 as [C7h C7m].
    destruct (Hhas C7h) as (Tt & Tz & Tb & Td).
    destruct (proj1 Ht Tt) as ([HFt [Hgt _]] & _ & _ & _).
    destruct (proj2 Ht Tt) as (Hlt2 & _).
    destruct (eval (tL (xt t)) (add (qB s) (wc (edlast e)))) as [[ad bd]|] eqn:Ee; [|discriminate C7e].
    apply ltb_spec_W in C7e.
    assert (Fad : fits ad = true).
    { destruct (eval_spec _ _ _ _ HFt Hgt FDL Ee) as (X & _). exact X. }
    rewrite val_add_c in C7e by (exact Fad || (vm_compute; reflexivity)). change (phi 3%uint63) with 3 in C7e.
    assert (XD := x_det_hyp (phi (qz s)) t (qB s) (phi (ed2 e)) (phi (edlast e)) (phi (edres e)) (add (qB s) (wc (edlast e))) ad bd Ht Tt Tz Tb
      ltac:(rewrite Td, Kd2; reflexivity)
      ltac:(destruct (lv_bounds _ HFt) as (_ & _ & _ & Bbs & _ & _); exact (low2_det _ _ _ SB Bbs C7m))
      (proj1 (phi_bd63 (edlast e)))
      ltac:(apply val_add_c; [exact SB|clear - BDL; lia]) FDL Ee C7e SB).
    rewrite <- EQ in XD. cbv beta iota in XD. destruct XD as (D0 & D1 & DC & CE0 & CE1 & CE2 & XDt).
    cbv beta iota zeta.
    exact (xblock_finish A0 B0 s xc0 xe m1 Q0 Q1 Q2 (tlen t) D0 D1 DC Hs N3 Mm1 Hxc Eb He Ez Ec Kra Krb CGm Hreg C6 (fun _ => XDt) CE0 CE1 CE2 (proj2 Hlt2) FBn MY2 Vbn).
  - injection EQ as -> -> ->. cbv beta iota zeta.
    refine (xblock_finish A0 B0 s xc0 xe m1 [] [] [] 0%uint63 0 0 0 Hs N3 Mm1 Hxc Eb He Ez Ec Kra Krb CGm Hreg C6 _ (cong_refl PM 0) (cong_refl PM 0) (cong_refl PM 0) ltac:(vm_compute; reflexivity) FBn MY2 Vbn).
    intros X. change (edet (xs xe)) with (edet e) in X. rewrite Ed in X. discriminate X.
Qed.

(** ** One slow sweep, by the map itself, with its count and cost *)
Fixpoint xzsweep (f : nat) (a b : Z) : option (Z * Z * Z * Z) :=
  match f with
  | O => None
  | S f =>
    match aStep a b with
    | None => None
    | Some (a1, b1, r) =>
      if (a1 =? 6) || (a1 =? 22) then Some (a1, b1, 1, r)
      else match xzsweep f a1 b1 with Some (a2, b2, n, r2) => Some (a2, b2, 1 + n, r + r2) | None => None end
    end
  end.
Lemma xzsweep_sound f : forall a b a1 b1 n r, xzsweep f a b = Some (a1, b1, n, r) -> Reach a b a1 b1 n r /\ (a1 = 6 \/ a1 = 22).
Proof.
  induction f as [|f IH]; intros a b a1 b1 n r H; [discriminate|].
  cbn [xzsweep] in H. destruct (aStep a b) as [[[a2 b2] r1]|] eqn:E; [|discriminate].
  destruct ((a2 =? 6) || (a2 =? 22)) eqn:C.
  - injection H as <- <- <- <-. split; [exact (xstep _ _ _ _ _ E)|]. apply orb_prop in C. destruct C as [C|C]; apply Z.eqb_eq in C; [left|right]; exact C.
  - destruct (xzsweep f a2 b2) as [[[[a3 b3] n3] r3]|] eqn:E2; [|discriminate]. injection H as <- <- <- <-.
    destruct (IH _ _ _ _ _ _ E2) as [H1 H2]. split; [|exact H2]. econstructor; [exact E|exact H1].
Qed.

Definition xslow_sweep (s : XSt) : XSt :=
  match xzsweep Wfuel (phi (qz s)) (val (qB s)) with
  | Some (a1, b1, n, r) =>
    let B1 := w_of_z b1 in let N := w_of_z n in
    if (val B1 =? b1) && fits B1 && (val N =? n) then xmove s (of_Z a1) B1 2 N (lz r) else xset_stat s 4
  | None => xset_stat s 4
  end.

Lemma xslow_sweep_sound A0 B0 s : xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xst_ok A0 B0 (xslow_sweep s) /\ xpost (qz s) (qB s) (xslow_sweep s).
Proof.
  intros Hs N3. unfold xslow_sweep. generalize (xzsweep_sound Wfuel (phi (qz s)) (val (qB s))). intros Hz.
  destruct (xzsweep Wfuel (phi (qz s)) (val (qB s))) as [[[[a1 b1] n] r]|];
    [|split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]].
  destruct (Hz _ _ _ _ eq_refl) as [R Ha]. clear Hz. cbv zeta.
  destruct ((val (w_of_z b1) =? b1) && fits (w_of_z b1) && (val (w_of_z n) =? n)) eqn:C;
    [|split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]].
  apply andb_prop in C. destruct C as [C Cn]. apply andb_prop in C. destruct C as [C F]. apply Z.eqb_eq in C, Cn.
  assert (Pa : phi (of_Z a1) = a1) by (destruct Ha as [-> | ->]; reflexivity).
  split; [|apply xpost_move_hop].
  apply (xmove_ok A0 B0 s (of_Z a1) (w_of_z b1) 2%uint63 (w_of_z n) (lz r) r Hs N3).
  - apply int_ne; reflexivity.
  - exact F.
  - rewrite Pa; exact Ha.
  - rewrite Pa, C, Cn. exact R.
  - apply lc_z.
Qed.

(** ** The recursion over the top of the tree *)
Fixpoint xnode (f : nat) (L : XLv) (s : XSt) : XSt :=
  match f with
  | O => xset_stat s 2
  | S f =>
    let run_child := fun (c : XLv) (s : XSt) =>
      if lv_fits (xl c) then
        let '(m, os) := xtry_block c s in
        match os with
        | Some s1 => s1
        | None => xnode f c (xset_mem s m)
        end
      else xslow_sweep s in
    if (1099511627000 <=? xlen L)%uint63 then xslow_sweep s else
    let L0 := xl L in
    match eval L0 (qB s) with
    | None => s
    | Some (a, b) =>
      let B := qB s in
      let a3 := add a (wc 3) in
      if ltb a3 b then
        let s1 := run_child (xchildD L a b B) s in
        if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1
      else if eqb a3 b then
        let '(e0, _, _) := xshift L (sub B (lbase L0)) in xhalt s a (wc (xlen L)) e0
      else if ltb b (wc 5) then xslow_sweep s
      else if ((low2 b) land 1 =? 1)%uint63 then
        if eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L0) (wc 1) || leb (lthr L0) (add b (wc 1))) then xslow_sweep s
        else
          let isu := (low2 (add (sub a b) (wc 5)) =? 2)%uint63 in
          let s1 := run_child (xchildUV L a b B isu) s in
          if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1
      else
        let L' := xrebase L a b B in
        if lv_fits (xl L') && fits (add (lc L0) (wc 7)) && fits (sub (lc L0) (wc 2)) then
          let s1 := xdo_stop s L' in
          if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1
        else xslow_sweep s
    end
  end.

Definition xinv (L : XLv) (s : XSt) : Prop :=
  xlv_ok (phi (qz s)) L /\ val (lbase (xl L)) <= val (qB s) /\ (val (qB s) - val (lbase (xl L))) mod 4 = 0.

Lemma xpost_trans z0 B s1 s2 : qstat s1 = 0%uint63 -> xpost z0 B s1 -> xpost (qz s1) (qB s1) s2 -> xpost z0 B s2.
Proof.
  intros E P1 P2 X. destruct (P1 E) as (E1 & L1 & M1). destruct (P2 X) as (E2 & L2 & M2).
  split; [rewrite E2; exact E1|]. split; [clear - L1 L2; lia|].
  replace (val (qB s2) - val B) with ((val (qB s2) - val (qB s1)) + (val (qB s1) - val B)) by ring. apply mod_add0; assumption.
Qed.
Lemma stat0_ne3 s : qstat s = 0%uint63 -> qstat s <> 3%uint63.
Proof. intros E. rewrite E. apply int_ne. reflexivity. Qed.

Section XNode.
Variables (A0 B0 : Z) (f : nat).
Hypothesis IH : forall L s, xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xinv L s -> xst_ok A0 B0 (xnode f L s) /\ xpost (qz s) (qB s) (xnode f L s).

Lemma xchild_sound c s : xst_ok A0 B0 s -> qstat s <> 3%uint63 -> lbase (xl c) = qB s -> (lv_fits (xl c) = true -> xlv_ok (phi (qz s)) c) ->
  let X := (if lv_fits (xl c) then
      let '(m, os) := xtry_block c s in
      match os with
      | Some s1 => s1
      | None => xnode f c (xset_mem s m)
      end
    else xslow_sweep s) in
  xst_ok A0 B0 X /\ xpost (qz s) (qB s) X.
Proof.
  intros Hs N3 Eb Hc. cbv zeta. destruct (lv_fits (xl c)) eqn:F; [|apply xslow_sweep_sound; assumption].
  specialize (Hc eq_refl).
  destruct (xtry_block c s) as [m os] eqn:T. destruct (xtry_block_sound _ _ _ _ _ _ Hs N3 Hc Eb T) as [Hm Ho].
  destruct os as [s1|]; [exact (Ho s1 eq_refl)|].
  apply (IH c (xset_mem s m)); [apply xst_mem; assumption|exact N3|].
  split; [exact Hc|]. cbn [qB xset_mem]. rewrite Eb. split; [clear; lia|]. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma xcont_sound L s s1 : xst_ok A0 B0 s -> xinv L s -> xst_ok A0 B0 s1 -> xpost (qz s) (qB s) s1 ->
  let X := if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1 in
  xst_ok A0 B0 X /\ xpost (qz s) (qB s) X.
Proof.
  intros Hs [HL [Hl Hm]] H1 P1. cbv zeta. destruct (qstat s1 =? 0)%uint63 eqn:C; [|split; assumption].
  apply Uint63.eqb_spec in C. destruct (P1 C) as (E & L1 & M1).
  assert (I1 : xinv L s1).
  { split; [rewrite E; exact HL|]. split; [clear - Hl L1; lia|].
    replace (val (qB s1) - val (lbase (xl L))) with ((val (qB s1) - val (qB s)) + (val (qB s) - val (lbase (xl L)))) by ring. apply mod_add0; assumption. }
  destruct (IH L s1 H1 (stat0_ne3 _ C) I1) as [R1 R2]. split; [exact R1|]. eapply xpost_trans; [exact C|exact P1|exact R2].
Qed.
End XNode.

Lemma xstay_post z0 B s : qz s = z0 -> qB s = B -> xpost z0 B s.
Proof. intros <- <- _. split; [reflexivity|]. split; [lia|]. rewrite Z.sub_diag. reflexivity. Qed.

Theorem xnode_sound A0 B0 f : forall L s, xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xinv L s -> xst_ok A0 B0 (xnode f L s) /\ xpost (qz s) (qB s) (xnode f L s).
Proof.
  induction f as [|f IH]; intros L s Hs N3 HI.
  { cbn [xnode]. split; [apply xst_stat; [exact Hs|exact N3|apply int_ne; reflexivity]|apply xpost_fail; reflexivity]. }
  cbn [xnode].
  destruct (1099511627000 <=? xlen L)%uint63 eqn:Cn; [apply xslow_sweep_sound; assumption|]. apply leb_false in Cn. change (phi 1099511627000%uint63) with 1099511627000 in Cn.
  pose proof HI as [HL [Hl Hm]]. pose proof HL as (HF & Hg & Hth & Hsum & Hlen & _).
  pose proof Hs as (SB & Sz & _).
  destruct (eval (xl L) (qB s)) as [[a b]|] eqn:He; [|split; [exact Hs|apply xstay_post; reflexivity]].
  destruct (eval_spec _ _ _ _ HF Hg SB He) as (Fa & Fb & Va & Vb & Vt).
  assert (V3 : val (add a (wc 3)) = val a + 3) by (rewrite val_add_c by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  assert (Rstep : forall s1, xst_ok A0 B0 s1 /\ xpost (qz s) (qB s) s1 ->
     xst_ok A0 B0 (if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1) /\ xpost (qz s) (qB s) (if (qstat s1 =? 0)%uint63 then xnode f L s1 else s1)).
  { intros s1 [H1 P1]. exact (xcont_sound A0 B0 f IH L s s1 Hs HI H1 P1). }
  destruct (ltb (add a (wc 3)) b) eqn:C1.
  { apply Rstep. apply (xchild_sound A0 B0 f IH); [exact Hs|exact N3| |].
    - unfold xchildD. destruct (xshift L (sub (qB s) (lbase (xl L)))) as [[e0 e1] e2]. reflexivity.
    - intros F. apply (xlvD _ L (qB s) a b HL SB Hl Hm He); [|exact F|lia]. apply ltb_spec_W in C1. clear - C1 V3. lia. }
  apply ltb_false_W in C1.
  destruct (eqb (add a (wc 3)) b) eqn:C2.
  { apply eqb_spec_W in C2. rewrite V3 in C2.
    pose proof (xlv_at _ L (qB s) a b HL SB Hl Hm He) as XA.
    destruct (xshift L (sub (qB s) (lbase (xl L)))) as [[e0 e1] e2]. destruct XA as (Q0 & Q1 & Q2 & C0 & _ & _ & HR).
    split; [|apply xpost_of; left; unfold xhalt; cbv zeta; destruct (fits (wc (xlen L)) && fits (add (qn s) (wc (xlen L)))); reflexivity].
    apply (xhalt_ok _ _ _ _ _ _ Q0 Hs N3); [|exact C0].
    pose proof (HR 0 ltac:(lia) ltac:(reflexivity) ltac:(rewrite Z.mul_0_r, Z.sub_0_r; exact Vt)) as X.
    rewrite val_wc. rewrite Z.add_0_r in X. eapply Rconv4; [exact X|ring|rewrite <- C2; ring|reflexivity|ring]. }
  apply eqb_false_W in C2. rewrite V3 in C2.
  destruct (ltb b (wc 5)) eqn:C3; [apply xslow_sweep_sound; assumption|].
  apply ltb_false_W in C3. rewrite val_wc in C3. change (phi 5%uint63) with 5 in C3.
  destruct ((low2 b) land 1 =? 1)%uint63 eqn:Od.
  - destruct (eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg (xl L)) (wc 1) || leb (lthr (xl L)) (add b (wc 1)))) eqn:C4; [apply xslow_sweep_sound; assumption|].
    apply orb_false_iff in C4. destruct C4 as [C4 C6]. apply orb_false_iff in C4. destruct C4 as [_ C5].
    apply negb_false_iff in C5, C6. apply leb_spec_W in C5. rewrite val_add_c in C5 by (exact Fb || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in C5.
    apply Rstep. apply (xchild_sound A0 B0 f IH); [exact Hs|exact N3| |].
    + unfold xchildUV. destruct (xshift L (sub (qB s) (lbase (xl L)))) as [[e0 e1] e2]. cbn [xl]. destruct (low2 (add (sub a b) (wc 5)) =? 2)%uint63; reflexivity.
    + intros F. apply (xlvUV _ L (qB s) a b _ HL SB Hl Hm He); try assumption.
      * apply low2_odd. exact Od.
      * apply orb_prop in C6. destruct C6 as [C6|C6].
        -- left. apply eqb_spec_W in C6. rewrite C6. reflexivity.
        -- right. apply leb_spec_W in C6. rewrite val_add_c in C6 by (exact Fb || (vm_compute; reflexivity)). exact C6.
      * apply low2_u; assumption.
      * apply low2_v; assumption.
      * lia.
  - destruct (lv_fits (xl (xrebase L a b (qB s))) && fits (add (lc (xl L)) (wc 7)) && fits (sub (lc (xl L)) (wc 2))) eqn:C4; [|apply xslow_sweep_sound; assumption].
    apply andb_prop in C4. destruct C4 as [C4 F2]. apply andb_prop in C4. destruct C4 as [_ F7].
    assert (Rb : xl (xrebase L a b (qB s)) = rebase (xl L) a b (qB s) /\ xlen (xrebase L a b (qB s)) = xlen L).
    { unfold xrebase. destruct (xshift L (sub (qB s) (lbase (xl L)))) as [[e0 e1] e2]. split; reflexivity. }
    destruct Rb as [Rb1 Rb2].
    apply Rstep. apply xdo_stop_sound.
    + exact Hs.
    + exact N3.
    + exact (xrebase_ok _ L (qB s) a b HL SB Hl Hm He).
    + rewrite Rb1. reflexivity.
    + rewrite Rb1. exact Vt.
    + rewrite Rb1. cbn [lb la rebase]. clear - C1 C2 V3. lia.
    + rewrite Rb1. apply low2_even. exact Od.
    + rewrite Rb1. exact F7.
    + rewrite Rb1. exact F2.
    + rewrite Rb2. lia.
Qed.

Fixpoint xtop (f : nat) (s : XSt) : XSt :=
  match f with
  | O => s
  | S f =>
    let s1 := xnode Nfuel (xroot (qz s) (qB s)) (xset_stat s 0) in
    if (qstat s1 =? 2)%uint63 then
      if leb (qY s1) (qB s1) then s1 else xtop f s1
    else s1
  end.
Fixpoint xtop2 (f : nat) (s : XSt) : XSt :=
  match f with
  | O => s
  | S f =>
    let s1 := xtop Tfuel s in
    if (qstat s1 =? 2)%uint63 && ltb (qB s1) (qY s1) then xtop2 f s1 else s1
  end.

Lemma stat2_ne3 s : (qstat s =? 2)%uint63 = true -> qstat s <> 3%uint63.
Proof. intros E. apply Uint63.eqb_spec in E. rewrite E. apply int_ne. reflexivity. Qed.

Lemma xtop_sound A0 B0 f : forall s, xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xst_ok A0 B0 (xtop f s).
Proof.
  induction f as [|f IH]; intros s Hs N3; [exact Hs|]. cbn [xtop].
  pose proof Hs as (SB & Sz & _).
  assert (I : xinv (xroot (qz s) (qB s)) (xset_stat s 0)).
  { split; [exact (xroot_ok _ _ SB Sz)|]. cbn [qB xset_stat xroot xl lbase root]. split; [clear; lia|]. rewrite Z.sub_diag. reflexivity. }
  destruct (xnode_sound A0 B0 Nfuel _ _ (xst_stat _ _ s 0%uint63 Hs N3 ltac:(apply int_ne; reflexivity)) ltac:(apply int_ne; reflexivity) I) as [R _].
  destruct (qstat (xnode Nfuel (xroot (qz s) (qB s)) (xset_stat s 0)) =? 2)%uint63 eqn:E2; [|exact R].
  destruct (leb _ _); [exact R|apply IH; [exact R|exact (stat2_ne3 _ E2)]].
Qed.
Lemma xtop2_sound A0 B0 f : forall s, xst_ok A0 B0 s -> qstat s <> 3%uint63 -> xst_ok A0 B0 (xtop2 f s).
Proof.
  induction f as [|f IH]; intros s Hs N3; [exact Hs|]. cbn [xtop2].
  pose proof (xtop_sound A0 B0 Tfuel s Hs N3) as R.
  destruct ((qstat (xtop Tfuel s) =? 2)%uint63 && ltb (qB (xtop Tfuel s)) (qY (xtop Tfuel s))) eqn:C; [|exact R].
  apply andb_prop in C. destruct C as [C _]. apply IH; [exact R|exact (stat2_ne3 _ C)].
Qed.

Definition xstart (z : int) (B Y : W) : XSt := mkXS z B 0 (wc 0) noxterm noxterm (xmem0 0%uint63) Y (wc 0) [].
Lemma xstart_ok z B Y : (phi z = 6 \/ phi z = 22) -> fits B = true -> xst_ok (phi z) (val B) (xstart z B Y).
Proof.
  intros Hz F. unfold xstart, xst_ok. cbn [qz qB qstat qha qd6 qd22 qm qY qn qr].
  refine (conj F (conj Hz (conj (xmem0_ok _) (conj (noxterm_ok _) (conj (noxterm_ok _) (conj eq_refl (ex_intro _ 0 (conj (cong_refl PM 0) (conj _ _))))))))).
  - intros X. exfalso. revert X. apply int_ne. reflexivity.
  - intros _. change (val (wc 0)) with 0. apply Reach_refl.
Qed.

Definition xrun (z : int) (B Y : W) : XSt := xtop2 Tfuel (xstart z B Y).
Definition xrun_seg (z : int) (B : W) (z1 : int) (Y N : W) (V : Vec.V) : bool :=
  let s := xrun z B Y in negb (qstat s =? 3)%uint63 && (qz s =? z1)%uint63 && eqb (qB s) Y && eqb (qn s) N && Vec.veqb (Vec.of_list (qr s)) V.
Definition xrun_halt_at (z : int) (B Y a N : W) (V : Vec.V) : bool :=
  let s := xrun z B Y in (qstat s =? 3)%uint63 && eqb (qha s) a && eqb (qn s) N && Vec.veqb (Vec.of_list (qr s)) V.

Theorem xrun_seg_sound z B z1 Y N V : good z B = true -> xrun_seg z B z1 Y N V = true ->
  exists r, Reach (phi z) (val B) (phi z1) (val Y) (val N) r /\ cong PM (Vec.vval V) r.
Proof.
  intros G H. destruct (good_spec _ _ G) as [Hz F].
  pose proof (xtop2_sound _ _ Tfuel _ (xstart_ok z B Y Hz F) ltac:(cbn [xstart qstat]; apply int_ne; reflexivity)) as (_ & _ & _ & _ & _ & _ & r & Cr & _ & R).
  unfold xrun_seg, xrun in H. cbv zeta in H.
  apply andb_prop in H. destruct H as [H Ev]. apply andb_prop in H. destruct H as [H En]. apply andb_prop in H. destruct H as [H EB]. apply andb_prop in H. destruct H as [N3 Ez].
  apply negb_true_iff in N3. apply eqb_true in Ez. apply eqb_spec_W in EB, En. apply Vec.veqb_eq in Ev.
  exists r. split.
  - rewrite <- Ez, <- EB, <- En. apply R. apply int_ne. exact N3.
  - rewrite <- Ev. eapply cong_trans; [apply Vec.of_list_spec|exact Cr].
Qed.

Theorem xrun_halt_at_sound z B Y a N V : good z B = true -> xrun_halt_at z B Y a N V = true ->
  exists r, Reach (phi z) (val B) (val a) (val a + 3) (val N) r /\ cong PM (Vec.vval V) r.
Proof.
  intros G H. destruct (good_spec _ _ G) as [Hz F].
  pose proof (xtop2_sound _ _ Tfuel _ (xstart_ok z B Y Hz F) ltac:(cbn [xstart qstat]; apply int_ne; reflexivity)) as (_ & _ & _ & _ & _ & _ & r & Cr & R & _).
  unfold xrun_halt_at, xrun in H. cbv zeta in H.
  apply andb_prop in H. destruct H as [H Ev]. apply andb_prop in H. destruct H as [H En]. apply andb_prop in H. destruct H as [S3 Ea].
  apply Uint63.eqb_spec in S3. apply eqb_spec_W in Ea, En. apply Vec.veqb_eq in Ev.
  exists r. split.
  - rewrite <- Ea, <- En. exact (R S3).
  - rewrite <- Ev. eapply cong_trans; [apply Vec.of_list_spec|exact Cr].
Qed.

Definition xresult (s : XSt) := (phi (qstat s), phi (qz s), val (qB s), val (qha s), val (qn s), Vec.of_list (qr s)).
