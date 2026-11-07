(** Block lemmas with exact counts: a cost beside the shape of [HCore], and what it means. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
Import ListNotations.
From BB6 Require Import Map Walk Num.
From BF Require Import Ints HLines HCore XCost.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Record Cost := mkC { en : int; em1 : int; em2 : P5; eapps : int; end_ : int; emd1 : int; emd2 : P5; ep : Poly }.
Record XEnt := mkX { xs : Ent; xk : Cost }.

Definition cost_bd (c : Cost) : Prop :=
  phi (en c) < 1073741824 /\ phi (em1 c) < 1152921504606846976 /\ good5 1073741824 (em2 c) /\ phi (eapps c) < 1152921504606846976 /\
  phi (end_ c) < 1073741824 /\ phi (emd1 c) < 1152921504606846976 /\ good5 1073741824 (emd2 c) /\ pgood 1073741824 (ep c).

Definition XPre (a0 B a b g Ym len p0 p1 p2 : Z) : Prop :=
  forall y, 0 <= y <= Ym -> y mod 4 = 0 -> Reach a0 (B + y) (a - (g - 1) * y) (b + g * y) len (p0 + p1 * y + p2 * (y * y)).
Definition XDet (dz a0 B d2 dl dres len2 d0 d1 dc : Z) : Prop :=
  forall y, 0 <= y <= dl -> y mod 4 = dres -> Reach dz (B + y) a0 (B + y + d2) len2 (d0 + d1 * y + dc * (y * y)).

Definition totn (c : Cost) (len len2 : Z) : Z := phi (en c) * len + phi (eapps c) + phi (end_ c) * len2.
Definition totr (c : Cost) (p0 p1 p2 d0 d1 dc b S g : Z) : Z :=
  p0 * phi (en c) + p1 * phi (em1 c) + p2 * val5 (em2 c) + pval (ep c) b S g + d0 * phi (end_ c) + d1 * phi (emd1 c) + dc * val5 (emd2 c).

Definition X_sem (x : XEnt) : Prop :=
  forall B a b g len p0 p1 p2 len2 d0 d1 dc,
    a + b = B + phi (ec (xs x)) -> a mod 4 = phi (era (xs x)) -> b mod 4 = phi (erb (xs x)) ->
    1 <= g -> phi (eGm (xs x)) <= g -> reg (xs x) b (a + b) g ->
    XPre (phi (ez (xs x))) B a b g (phi (elast (xs x))) len p0 p1 p2 ->
    (edet (xs x) = true -> XDet (28 - phi (ez (xs x))) (phi (ez (xs x))) B (phi (ed2 (xs x))) (phi (edlast (xs x))) (phi (edres (xs x))) len2 d0 d1 dc) ->
    Reach (phi (ez (xs x))) B (phi (ez (xs x))) (B + phi (eY (xs x))) (totn (xk x) len len2) (totr (xk x) p0 p1 p2 d0 d1 dc b (a + b) g).

Definition x_ok (x : XEnt) : Prop := ent_ok (xs x) /\ cost_bd (xk x) /\ X_sem x.

(** ** Letters with their costs *)
Lemma xstep a b a1 b1 r : aStep a b = Some (a1, b1, r) -> Reach a b a1 b1 1 r.
Proof. intros H. replace 1 with (1 + 0) by ring. replace r with (r + 0) by ring. econstructor; [exact H|constructor]. Qed.
Lemma XD a b : a + 3 < b -> Reach a b (2 * a + 6) (b - a - 3) 1 (-30 * a + 18).
Proof. intros H. apply xstep. apply L_D. exact H. Qed.
Lemma XU a b : b mod 2 = 1 -> (a - b + 5) mod 4 = 2 -> 5 <= b -> b + 1 <= a -> Reach a b (a - b + 11) (2 * b - 4) 1 (4 * b * (a + b) - 11 * a + 29 * b + 13).
Proof.
  intros H1 H2 H3 H4. apply xstep. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [lia|]. destruct (Z.eqb_spec b 3) as [|_]; [lia|].
  rewrite H1. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a + 1)) as [|_]; [lia|].
  rewrite H2. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma XV a b : b mod 2 = 1 -> (a - b + 5) mod 4 <> 2 -> 5 <= b -> b + 1 <= a -> Reach a b (a - b + 19) (2 * b - 8) 1 (4 * b * (a + b) - 19 * a + 37 * b - 29).
Proof.
  intros H1 H2 H3 H4. apply xstep. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [lia|]. destruct (Z.eqb_spec b 3) as [|_]; [lia|].
  rewrite H1. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a + 1)) as [|_]; [lia|].
  destruct (Z.eqb_spec ((a - b + 5) mod 4) 2) as [|_]; [lia|]. reflexivity.
Qed.
Lemma XW a b : b mod 2 = 0 -> b < a + 3 -> (a - b) mod 4 = 2 -> Reach a b 6 (a + b + 7) 1 (2 * a * a + 6 * b * b + 39 * a - 9 * b + 378).
Proof.
  intros H1 H2 H3. apply xstep. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [subst b; discriminate|]. destruct (Z.eqb_spec b 3) as [|_]; [subst b; discriminate|].
  rewrite H1. change (0 =? 1) with false. rewrite H3. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma XX a b : b mod 2 = 0 -> b < a + 3 -> (a - b) mod 4 <> 2 -> Reach a b 22 (a + b - 2) 1 (2 * a * a + 6 * b * b + 39 * a - 9 * b + 274).
Proof.
  intros H1 H2 H3. apply xstep. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [subst b; discriminate|]. destruct (Z.eqb_spec b 3) as [|_]; [subst b; discriminate|].
  rewrite H1. change (0 =? 1) with false.
  destruct (Z.eqb_spec ((a - b) mod 4) 2) as [|_]; [lia|]. reflexivity.
Qed.

Lemma Rconv a b a1 b1 n r n2 r2 : Reach a b a1 b1 n r -> n = n2 -> r = r2 -> Reach a b a1 b1 n2 r2.
Proof. intros H -> ->. exact H. Qed.

Definition qcost (xz zz kx kz k0 x w : Z) : Z := 32 * (x * x) - xz * (x * w) + zz * (w * w) - kx * x + kz * w + k0.

(** One round of a stop: one letter and a terminal letter, exact. *)
Lemma xterminal a b : b mod 2 = 0 -> b < a + 3 ->
  ((a - b) mod 4 = 2 /\ Reach a b 6 (a + b + 7) 1 (2 * a * a + 6 * b * b + 39 * a - 9 * b + 378)) \/
  ((a - b) mod 4 <> 2 /\ Reach a b 22 (a + b - 2) 1 (2 * a * a + 6 * b * b + 39 * a - 9 * b + 274)).
Proof.
  intros H1 H2. destruct (Z.eq_dec ((a - b) mod 4) 2) as [E|E].
  - left. split; [exact E|]. apply XW; assumption.
  - right. split; [exact E|]. apply XX; assumption.
Qed.

Lemma xround_U a b D1 ra1 rb1 z K :
  (a - b + 5) mod 4 = 2 -> ra1 = (a - b + 11) mod 4 -> rb1 = (2 * b - 4) mod 4 ->
  b mod 2 = 1 -> 5 <= b -> b + 1 <= a -> 4 * b < a + b + 18 ->
  (((ra1 + 4 - rb1) mod 4 = 2 /\ z = 6 /\ D1 = 14 /\ K = 378) \/ ((ra1 + 4 - rb1) mod 4 <> 2 /\ z = 22 /\ D1 = 5 /\ K = 274)) ->
  Reach a b z (a + b + D1) 2 (qcost 4 2 240 72 (816 + K) b (a + b)).
Proof.
  intros Hu H2 H3 Odd B5 Ba Bs Ht.
  assert (R1 := XU a b Odd Hu B5 Ba).
  assert (E1 : (2 * b - 4) mod 2 = 0) by (Z.div_mod_to_equations; lia).
  assert (T : (a - b + 11 - (2 * b - 4)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
  destruct (xterminal (a - b + 11) (2 * b - 4) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R1 R2) as R.
  - destruct Ht as [(Hc0 & -> & -> & ->)|(Hc0 & _)]; [|congruence].
    replace (a + b + 14) with (a - b + 11 + (2 * b - 4) + 7) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
  - destruct Ht as [(Hc0 & _)|(Hc0 & -> & -> & ->)]; [congruence|].
    replace (a + b + 5) with (a - b + 11 + (2 * b - 4) - 2) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
Qed.
Lemma xround_V a b D1 ra1 rb1 z K :
  (a - b + 5) mod 4 <> 2 -> ra1 = (a - b + 19) mod 4 -> rb1 = (2 * b - 8) mod 4 ->
  b mod 2 = 1 -> 5 <= b -> b + 1 <= a -> 4 * b < a + b + 18 ->
  (((ra1 + 4 - rb1) mod 4 = 2 /\ z = 6 /\ D1 = 18 /\ K = 378) \/ ((ra1 + 4 - rb1) mod 4 <> 2 /\ z = 22 /\ D1 = 9 /\ K = 274)) ->
  Reach a b z (a + b + D1) 2 (qcost 4 2 384 96 (1890 + K) b (a + b)).
Proof.
  intros Hv H2 H3 Odd B5 Ba Bs Ht.
  assert (R1 := XV a b Odd Hv B5 Ba).
  assert (E1 : (2 * b - 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
  assert (T : (a - b + 19 - (2 * b - 8)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
  destruct (xterminal (a - b + 19) (2 * b - 8) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R1 R2) as R.
  - destruct Ht as [(Hc0 & -> & -> & ->)|(Hc0 & _)]; [|congruence].
    replace (a + b + 18) with (a - b + 19 + (2 * b - 8) + 7) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
  - destruct Ht as [(Hc0 & _)|(Hc0 & -> & -> & ->)]; [congruence|].
    replace (a + b + 9) with (a - b + 19 + (2 * b - 8) - 2) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
Qed.
Lemma xround_D a b D1 ra1 rb1 z K :
  ra1 = (2 * a + 6) mod 4 -> rb1 = (b - a - 3) mod 4 -> a + 3 < b -> 4 * b < 3 * (a + b) + 12 -> rb1 mod 2 = 0 ->
  (((ra1 + 4 - rb1) mod 4 = 2 /\ z = 6 /\ D1 = 10 /\ K = 378) \/ ((ra1 + 4 - rb1) mod 4 <> 2 /\ z = 22 /\ D1 = 1 /\ K = 274)) ->
  Reach a b z (a + b + D1) 2 (qcost 40 14 186 141 (405 + K) b (a + b)).
Proof.
  intros H2 H3 G1 G2 Ev Ht.
  assert (R1 := XD a b G1).
  assert (E1 : (b - a - 3) mod 2 = 0) by (subst rb1; Z.div_mod_to_equations; lia).
  assert (T : (2 * a + 6 - (b - a - 3)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
  destruct (xterminal (2 * a + 6) (b - a - 3) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R1 R2) as R.
  - destruct Ht as [(Hc0 & -> & -> & ->)|(Hc0 & _)]; [|congruence].
    replace (a + b + 10) with (2 * a + 6 + (b - a - 3) + 7) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
  - destruct Ht as [(Hc0 & _)|(Hc0 & -> & -> & ->)]; [congruence|].
    replace (a + b + 1) with (2 * a + 6 + (b - a - 3) - 2) by ring. eapply Rconv; [exact R|ring|]. unfold qcost. ring.
Qed.

(** ** Rounds, summed in closed form *)
Fixpoint s1 (T : nat) : Z := match T with O => 0 | S n => s1 n + Z.of_nat n end.
Fixpoint s2 (T : nat) : Z := match T with O => 0 | S n => s2 n + Z.of_nat n * Z.of_nat n end.
Lemma s1_form T : 2 * s1 T = Z.of_nat T * (Z.of_nat T - 1).
Proof. induction T as [|n IH]; [reflexivity|]. cbn [s1]. rewrite Nat2Z.inj_succ. nia. Qed.
Lemma s2_form T : 6 * s2 T = (Z.of_nat T - 1) * Z.of_nat T * (2 * Z.of_nat T - 1).
Proof. induction T as [|n IH]; [reflexivity|]. cbn [s2]. rewrite Nat2Z.inj_succ. nia. Qed.

Lemma rounds_poly a0 B y D n0 A1 A2 A3 (T : nat) :
  (forall t, 0 <= t < Z.of_nat T -> Reach a0 (B + y + t * D) a0 (B + y + (t + 1) * D) n0 (A1 + A2 * (y + t * D) + A3 * ((y + t * D) * (y + t * D)))) ->
  Reach a0 (B + y) a0 (B + y + Z.of_nat T * D) (Z.of_nat T * n0)
    (A1 * Z.of_nat T + A2 * (y * Z.of_nat T + D * s1 T) + A3 * (D * D * s2 T + y * y * Z.of_nat T + 2 * y * D * s1 T)).
Proof.
  induction T as [|n IH]; intros H.
  { replace (B + y + Z.of_nat 0 * D) with (B + y) by (cbn; ring). eapply Rconv; [apply Reach_refl|cbn; ring|cbn [s1 s2]; cbn; ring]. }
  pose proof (IH (fun t Ht => H t ltac:(lia))) as R1.
  pose proof (H (Z.of_nat n) ltac:(lia)) as R2.
  pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ R1 R2) as R.
  replace (B + y + Z.of_nat (S n) * D) with (B + y + (Z.of_nat n + 1) * D) by lia.
  eapply Rconv; [exact R| |].
  - rewrite Nat2Z.inj_succ. ring.
  - cbn [s1 s2]. rewrite Nat2Z.inj_succ. ring.
Qed.

(** ** A stop: the shape from [stop_rounds], the cost beside it *)
Definition x_stop (bx : XEnt) (v : Env) (dl : bool) (beta : int) : option XEnt :=
  let b := xs bx in let c := xk bx in
  match stop_rounds b v dl beta with
  | None => None
  | Some s =>
    let y := eY b in
    let kind := if dl then 0%uint63 else kind_of (era b) (erb b) in
    let cc := (ec b + kcost kind)%uint63 in
    let rae := ra_next (era b) (erb b) kind in let rbe := rb_next (era b) (erb b) kind in
    let e_ := if dl then 3%uint63 else 1%uint63 in
    let isw := (((rae + 4 - rbe) land 3) =? 2)%uint63 in
    let z := if isw then 6%uint63 else 22%uint63 in
    let D1 := if isw then (cc + 7)%uint63 else (cc - 2)%uint63 in
    let K := if isw then 378%uint63 else 274%uint63 in
    let direct := (z =? vz v)%uint63 && ((D1 land 3) =? 0)%uint63 in
    let DD := if direct then D1 else (D1 + vd2 v)%uint63 in
    let gapn := (((e_ * eW b) >> 2) + VOFF - beta - (y << 28) - 9)%uint63 in
    let T := (((gapn - VOFF) >> 28) / DD + 1)%uint63 in
    if (1048576 <=? T)%uint63 then None else
    let S1 := (T * (T - 1) / 2)%uint63 in
    let S2 := ((T - 1) * T * (2 * T - 1) / 6)%uint63 in
    let t1 := (y * T + DD * S1)%uint63 in
    let dd1 := addk zero5 DD (pnat S2) in
    let dds := addk zero5 DD dd1 in
    let t2 := addk dds y (pnat (y * T + 2 * DD * S1)%uint63) in
    let yd := (y + D1)%uint63 in
    let dt1 := (yd * T + DD * S1)%uint63 in
    let dt2 := addk dds yd (pnat (yd * T + 2 * DD * S1)%uint63) in
    let p := if dl then stopQ 40 14 186 141 (405 + K)%uint63 (ep c) T t1 t2
             else if (kind =? 1)%uint63 then stopQ 4 2 240 72 (816 + K)%uint63 (ep c) T t1 t2
             else stopQ 4 2 384 96 (1890 + K)%uint63 (ep c) T t1 t2 in
    let m2 := add5 (em2 c) t2 in
    let md2 := if direct then emd2 c else add5 (emd2 c) dt2 in
    let nd := if direct then end_ c else (end_ c + T)%uint63 in
    let md1 := if direct then emd1 c else (emd1 c + dt1)%uint63 in
    let nn := (en c + T)%uint63 in let m1 := (em1 c + t1)%uint63 in let ap := (eapps c + 2 * T)%uint63 in
    if ok5 dd1 && ok5 t2 && ok5 m2 && (direct || ok5 dt2) && ok5 md2 && pok p && (nn <? 1073741824)%uint63 && (m1 <? 1152921504606846976)%uint63
       && (ap <? 1152921504606846976)%uint63 && (nd <? 1073741824)%uint63 && (md1 <? 1152921504606846976)%uint63 then
      Some (mkX s (mkC nn m1 m2 ap nd md1 md2 p))
    else None
  end.

Definition tsum1 (y D : Z) (T : nat) : Z := y * Z.of_nat T + D * s1 T.
Definition tsum2 (y D : Z) (T : nat) : Z := D * D * s2 T + y * y * Z.of_nat T + 2 * y * D * s1 T.

Lemma stop_sum z B y D T n0 p0 p1 p2 xz zz kx kz k0 b0 S g dt d0 d1 dc D1 :
  (forall t, 0 <= t < Z.of_nat T ->
     Reach z (B + y + t * D) z (B + y + (t + 1) * D) n0
       (p0 + p1 * (y + t * D) + p2 * ((y + t * D) * (y + t * D)) + qcost xz zz kx kz k0 (b0 + g * (y + t * D)) (S + (y + t * D))
        + dt * (d0 + d1 * (y + t * D + D1) + dc * ((y + t * D + D1) * (y + t * D + D1))))) ->
  Reach z (B + y) z (B + y + Z.of_nat T * D) (Z.of_nat T * n0)
    (p0 * Z.of_nat T + p1 * tsum1 y D T + p2 * tsum2 y D T
     + 32 * (Z.of_nat T * (b0 * b0) + 2 * tsum1 y D T * (b0 * g) + tsum2 y D T * (g * g))
     - xz * (Z.of_nat T * (b0 * S) + tsum1 y D T * (b0 + g * S) + tsum2 y D T * g)
     + zz * (Z.of_nat T * (S * S) + 2 * tsum1 y D T * S + tsum2 y D T)
     - kx * (Z.of_nat T * b0 + tsum1 y D T * g) + kz * (Z.of_nat T * S + tsum1 y D T) + k0 * Z.of_nat T
     + dt * (d0 * Z.of_nat T + d1 * tsum1 (y + D1) D T + dc * tsum2 (y + D1) D T)).
Proof.
  intros H.
  set (A1 := p0 + 32 * (b0 * b0) - xz * (b0 * S) + zz * (S * S) - kx * b0 + kz * S + k0 + dt * (d0 + d1 * D1 + dc * (D1 * D1))).
  set (A2 := p1 + 64 * b0 * g - xz * (b0 + g * S) + 2 * zz * S - kx * g + kz + dt * (d1 + 2 * dc * D1)).
  set (A3 := p2 + 32 * (g * g) - xz * g + zz + dt * dc).
  pose proof (rounds_poly z B y D n0 A1 A2 A3 T) as R.
  eapply Rconv; [apply R|ring|].
  - intros t Ht. eapply Rconv; [apply (H t Ht)|ring|]. unfold qcost, A1, A2, A3. ring.
  - unfold tsum1, tsum2, A1, A2, A3. ring.
Qed.

Lemma T_nat (T : Z) : 1 <= T -> Z.of_nat (Z.to_nat T) = T.
Proof. intros. apply Z2Nat.id. lia. Qed.

(** The moments' integer expressions, exactly. *)
Lemma s1_val (T : int) : 1 <= phi T < 1048576 -> phi (T * (T - 1) / 2)%uint63 = s1 (Z.to_nat (phi T)).
Proof.
  intros HT. rewrite div_spec. change (phi 2%uint63) with 2.
  assert (Em : phi (T - 1)%uint63 = phi T - 1) by pv.
  assert (Ep : phi (T * (T - 1))%uint63 = phi T * (phi T - 1)).
  { apply phi_of_cg; [apply cg_mul; [apply cg_refl|unfold cg; rewrite Em; reflexivity]|nia]. }
  rewrite Ep. pose proof (s1_form (Z.to_nat (phi T))) as F. rewrite T_nat in F by lia. rewrite <- F. rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.
Lemma s2_val (T : int) : 1 <= phi T < 1048576 -> phi ((T - 1) * T * (2 * T - 1) / 6)%uint63 = s2 (Z.to_nat (phi T)).
Proof.
  intros HT. rewrite div_spec. change (phi 6%uint63) with 6.
  assert (Em : phi (T - 1)%uint63 = phi T - 1) by pv.
  assert (Em2 : phi (2 * T - 1)%uint63 = 2 * phi T - 1) by pv.
  assert (B1 : 0 <= (phi T - 1) * phi T <= 1048576 * 1048576) by nia.
  assert (B2 : 0 <= (phi T - 1) * phi T * (2 * phi T - 1) <= 1048576 * 1048576 * 2097152).
  { split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]. }
  assert (Ep : phi ((T - 1) * T * (2 * T - 1))%uint63 = (phi T - 1) * phi T * (2 * phi T - 1)).
  { apply phi_of_cg; [apply cg_mul; [apply cg_mul; [unfold cg; rewrite Em; reflexivity|apply cg_refl]|unfold cg; rewrite Em2; reflexivity]|lia]. }
  rewrite Ep. pose proof (s2_form (Z.to_nat (phi T))) as F. rewrite T_nat in F by lia. rewrite <- F. rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma mul_bd x y X Y : 0 <= x <= X -> 0 <= y <= Y -> 0 <= x * y <= X * Y.
Proof. intros H1 H2. split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]. Qed.

Lemma XPre_mono a0 B a b g Y1 Y2 len p0 p1 p2 : Y1 <= Y2 -> XPre a0 B a b g Y2 len p0 p1 p2 -> XPre a0 B a b g Y1 len p0 p1 p2.
Proof. intros L H y Hy. apply H. lia. Qed.

(** The word at one visit: what a stop's kind decides. *)
Definition word_at (b : Ent) (dl : bool) (z D1 xz zz kx kz k0 : Z) : Prop :=
  forall B1 a1 b1, a1 + b1 = B1 + phi (ec b) -> phi (era b) = a1 mod 4 -> phi (erb b) = b1 mod 4 ->
    (if dl then a1 + 3 < b1 /\ 4 * b1 < 3 * (a1 + b1) + 12 else 5 <= b1 /\ b1 + 1 <= a1 /\ 4 * b1 < a1 + b1 + 18) ->
    Reach a1 b1 z (B1 + D1) 2 (qcost xz zz kx kz k0 b1 (a1 + b1)).

Lemma word_sound (b : Ent) (dl : bool) (kind cc rae rbe D1 K z : int) (isw : bool) :
  kind = (if dl then 0%uint63 else kind_of (era b) (erb b)) ->
  rae = ra_next (era b) (erb b) kind -> rbe = rb_next (era b) (erb b) kind ->
  phi cc = phi (ec b) + phi (kcost kind) ->
  isw = (((rae + 4 - rbe) land 3) =? 2)%uint63 ->
  z = (if isw then 6%uint63 else 22%uint63) -> K = (if isw then 378%uint63 else 274%uint63) ->
  (isw = true /\ phi D1 = phi cc + 7 \/ isw = false /\ phi D1 = phi cc - 2) ->
  phi rbe mod 2 = 0 -> (dl = false -> phi (erb b) mod 2 = 1) ->
  (dl = true /\ word_at b dl (phi z) (phi D1) 40 14 186 141 (405 + phi K)) \/
  (dl = false /\ (kind =? 1)%uint63 = true /\ word_at b dl (phi z) (phi D1) 4 2 240 72 (816 + phi K)) \/
  (dl = false /\ (kind =? 1)%uint63 = false /\ word_at b dl (phi z) (phi D1) 4 2 384 96 (1890 + phi K)).
Proof.
  intros Ekind Era Erb Ecc Eisw Ez EK ED1 Ev Odd.
  assert (BA : 0 <= phi rae < 4 /\ 0 <= phi rbe < 4).
  { subst rae rbe. unfold ra_next, rb_next. destruct (kind =? 0)%uint63; [|destruct (kind =? 1)%uint63]; rewrite !phi_land3; split; apply Z.mod_pos_bound; reflexivity. }
  assert (F : phi (rae + 4 - rbe)%uint63 = phi rae + 4 - phi rbe) by (apply phi_of_cg; [apply cg_sub; [apply cg_add; [apply cg_refl|reflexivity]|apply cg_refl]|lia]).
  assert (F2 : phi ((rae + 4 - rbe) land 3)%uint63 = (phi rae + 4 - phi rbe) mod 4) by (rewrite phi_land3, F; reflexivity).
  assert (Risw : ((phi rae + 4 - phi rbe) mod 4 = 2 /\ isw = true /\ phi z = 6 /\ phi K = 378 /\ phi D1 = phi cc + 7) \/ ((phi rae + 4 - phi rbe) mod 4 <> 2 /\ isw = false /\ phi z = 22 /\ phi K = 274 /\ phi D1 = phi cc - 2)).
  { subst z K. destruct isw eqn:Ci.
    - left. destruct ED1 as [[_ E]|[X _]]; [|discriminate]. split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|exact E]]]]. rewrite Eisw in *.
      symmetry in Eisw. apply eqb_true in Eisw. rewrite F2 in Eisw. exact Eisw.
    - right. destruct ED1 as [[X _]|[_ E]]; [discriminate|]. split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|exact E]]]]. intros X. rewrite <- F2 in X.
      assert (Y : ((rae + 4 - rbe) land 3)%uint63 = 2%uint63) by (apply to_Z_inj; exact X). rewrite Y in Eisw. discriminate. }
  destruct dl.
  - left. split; [reflexivity|]. subst kind. intros B1 a1 b1 HS Ra Rb [G1 G2].
    destruct (res_D (era b) (erb b) a1 b1 Ra Rb) as [E1 E2].
    assert (Ec3 : phi (kcost 0%uint63) = 3) by reflexivity. rewrite Ec3 in Ecc.
    subst rae rbe.
    replace (B1 + phi D1) with (a1 + b1 + (phi D1 - phi (ec b))) by lia.
    apply xround_D with (ra1 := phi (ra_next (era b) (erb b) 0)) (rb1 := phi (rb_next (era b) (erb b) 0)); try assumption.
    destruct Risw as [(C1 & _ & C3 & C4 & C5)|(C1 & _ & C3 & C4 & C5)].
    + left. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
    + right. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
  - right. subst kind. specialize (Odd eq_refl).
    assert (Hk : forall a1 b1, phi (era b) = a1 mod 4 -> phi (erb b) = b1 mod 4 -> b1 mod 2 = 1).
    { intros a1 b1 _ Rb. rewrite Rb in Odd. revert Odd. clear. intros Odd. Z.div_mod_to_equations. lia. }
    destruct (kind_of (era b) (erb b) =? 1)%uint63 eqn:Kk.
    + left. split; [reflexivity|]. split; [reflexivity|]. apply eqb_true in Kk. change (phi 1%uint63) with 1 in Kk.
      assert (Kv : kind_of (era b) (erb b) = 1%uint63) by (apply to_Z_inj; exact Kk).
      rewrite Kv in *. intros B1 a1 b1 HS Ra Rb (G1 & G2 & G3).
      assert (Ec7 : phi (kcost 1%uint63) = 7) by reflexivity. rewrite Ec7 in Ecc.
      destruct (res_kind (era b) (erb b) a1 b1 Ra Rb) as [[K1 K2]|[K1 K2]]; [|rewrite Kv in K1; discriminate K1].
      destruct (res_U (era b) (erb b) a1 b1 Ra Rb) as [E1 E2]. subst rae rbe.
      replace (B1 + phi D1) with (a1 + b1 + (phi D1 - phi (ec b))) by lia.
      apply xround_U with (ra1 := phi (ra_next (era b) (erb b) 1)) (rb1 := phi (rb_next (era b) (erb b) 1)); try assumption.
      * exact (Hk a1 b1 Ra Rb).
      * destruct Risw as [(C1 & _ & C3 & C4 & C5)|(C1 & _ & C3 & C4 & C5)].
        -- left. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
        -- right. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
    + right. split; [reflexivity|]. split; [reflexivity|]. intros B1 a1 b1 HS Ra Rb (G1 & G2 & G3).
      destruct (res_kind (era b) (erb b) a1 b1 Ra Rb) as [[K1 K2]|[K1 K2]].
      { assert (Kv : kind_of (era b) (erb b) = 1%uint63) by (apply to_Z_inj; exact K1). rewrite Kv in Kk. discriminate Kk. }
      assert (Kv : kind_of (era b) (erb b) = 2%uint63) by (apply to_Z_inj; exact K1). rewrite Kv in *.
      assert (Ec7 : phi (kcost 2%uint63) = 11) by reflexivity. rewrite Ec7 in Ecc.
      destruct (res_V (era b) (erb b) a1 b1 Ra Rb) as [E1 E2]. subst rae rbe.
      replace (B1 + phi D1) with (a1 + b1 + (phi D1 - phi (ec b))) by lia.
      apply xround_V with (ra1 := phi (ra_next (era b) (erb b) 2)) (rb1 := phi (rb_next (era b) (erb b) 2)); try assumption.
      * exact (Hk a1 b1 Ra Rb).
      * destruct Risw as [(C1 & _ & C3 & C4 & C5)|(C1 & _ & C3 & C4 & C5)].
        -- left. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
        -- right. split; [exact C1|]. split; [exact C3|]. split; [lia|exact C4].
Qed.

Lemma stop_r_eq PV T1 T2 DT1 DT2 t dt En Em1 Em2 End Emd1 Emd2 p0 p1 p2 d0 d1 dc b S g xz zz kx kz k0 :
  p0 * En + p1 * Em1 + p2 * Em2 + PV + d0 * End + d1 * Emd1 + dc * Emd2 +
  (p0 * t + p1 * T1 + p2 * T2 + 32 * (t * (b * b) + 2 * T1 * (b * g) + T2 * (g * g)) - xz * (t * (b * S) + T1 * (b + g * S) + T2 * g)
   + zz * (t * (S * S) + 2 * T1 * S + T2) - kx * (t * b + T1 * g) + kz * (t * S + T1) + k0 * t + dt * (d0 * t + d1 * DT1 + dc * DT2)) =
  p0 * (En + t) + p1 * (Em1 + T1) + p2 * (Em2 + T2)
  + (PV + 32 * (t * (b * b) + 2 * T1 * (b * g) + T2 * (g * g)) - xz * (t * (b * S) + T1 * (b + g * S) + T2 * g)
     + zz * (t * (S * S) + 2 * T1 * S + T2) - kx * (t * b + T1 * g) + kz * (t * S + T1) + k0 * t)
  + d0 * (End + dt * t) + d1 * (Emd1 + dt * DT1) + dc * (Emd2 + dt * DT2).
Proof. ring. Qed.

Lemma x_stop_sound bx v dl beta x : x_ok bx -> phi (vz v) = 6 \/ phi (vz v) = 22 -> x_stop bx v dl beta = Some x ->
  x_ok x /\ ec (xs x) = ec (xs bx) /\ era (xs x) = era (xs bx) /\ erb (xs x) = erb (xs bx) /\ ez (xs x) = ez (xs bx) /\ ed2 (xs x) = ed2 (xs bx) /\
  eW (xs x) = eW (xs bx) /\ eW1 (xs x) = eW1 (xs bx) /\ eW2 (xs x) = eW2 (xs bx).
Proof.
  destruct bx as [b c]. intros [Hok [Hc XS]] Hz Hx. unfold x_stop in Hx. cbn [xs xk] in *. cbv zeta in Hx.
  destruct (stop_rounds b v dl beta) as [s|] eqn:H; [|discriminate Hx].
  destruct (stop_sound _ _ _ _ _ Hok Hz H) as [Oks Facts].
  destruct Hok as [Bd _]. unfold stop_rounds in H. cbv zeta in H.
  destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  set (kind := if dl then 0%uint63 else kind_of (era b) (erb b)) in *.
  set (cc := (ec b + kcost kind)%uint63) in *.
  set (rae := ra_next (era b) (erb b) kind) in *.
  set (rbe := rb_next (era b) (erb b) kind) in *.
  set (e_ := if dl then 3%uint63 else 1%uint63) in *.
  destruct (negb ((rbe land 1) =? 0)%uint63 || (negb dl && negb ((erb b land 1) =? 1)%uint63) || (cc <? 8)%uint63 || (1099511627776 <=? cc)%uint63
     || negb ((ez b =? vz v)%uint63) || negb ((ed2 b =? vd2 v)%uint63)) eqn:G1; [discriminate|].
  repeat (apply orb_false_iff in G1; destruct G1 as [G1 ?]).
  rename H0 into G6. rename H1 into G5. rename H2 into G4. rename H3 into G3. rename H4 into G2.
  apply negb_false_iff in G1. apply negb_false_iff in G5. apply negb_false_iff in G6.
  apply ltb_false in G3. apply leb_false in G4. change (phi 8%uint63) with 8 in G3. change (phi 1099511627776%uint63) with 1099511627776 in G4.
  apply Uint63.eqb_spec in G5. apply Uint63.eqb_spec in G6.
  set (isw := ((rae + 4 - rbe) land 3 =? 2)%uint63) in *.
  set (z := if isw then 6%uint63 else 22%uint63) in *.
  set (D1 := if isw then (cc + 7)%uint63 else (cc - 2)%uint63) in *.
  set (direct := (z =? vz v)%uint63 && ((D1 land 3) =? 0)%uint63) in *.
  set (det := negb direct && vhas v && (z + vz v =? 28)%uint63 && (((D1 + vd2 v) land 3) =? 0)%uint63 && (vd2 v <? 1099511627776)%uint63) in *.
  destruct (direct || det) eqn:G7; [|discriminate].
  set (DD := if direct then D1 else (D1 + vd2 v)%uint63) in *.
  set (gapn := (((e_ * eW b) >> 2) + VOFF - beta - (eY b << 28) - 9)%uint63) in *.
  destruct (gapn <? VOFF)%uint63 eqn:G8; [discriminate|].
  set (T := (((gapn - VOFF) >> 28) / DD + 1)%uint63) in *.
  destruct ((2097152 <=? T)%uint63 || (T =? 0)%uint63) eqn:G9; [discriminate|].
  apply orb_false_iff in G9. destruct G9 as [G9 G10]. apply leb_false in G9. change (phi 2097152%uint63) with 2097152 in G9.
  assert (T1 : 1 <= phi T).
  { pose proof (phi_bd63 T). destruct (Z.eq_dec (phi T) 0) as [E|E]; [|lia].
    assert (TZ : T = 0%uint63) by (apply to_Z_inj; exact E). rewrite TZ in G10. discriminate. }
  clearbody T.
  set (ylast := (eY b + (T - 1) * DD)%uint63) in *.
  destruct (1073741824 <=? (ylast + DD))%uint63 eqn:G11; [discriminate|]. apply leb_false in G11. change (phi 1073741824%uint63) with TT in G11.
  (** values *)
  assert (Ee : phi e_ = 1 \/ phi e_ = 3) by (unfold e_; destruct dl; [right|left]; reflexivity).
  assert (Ek : phi (kcost kind) = 3 \/ phi (kcost kind) = 7 \/ phi (kcost kind) = 11).
  { unfold kcost. destruct (kind =? 0)%uint63; [left; reflexivity|]. destruct (kind =? 1)%uint63; [right; left; reflexivity|right; right; reflexivity]. }
  assert (Ecc : phi cc = phi (ec b) + phi (kcost kind)) by (unfold cc; pv).
  assert (ED1 : (isw = true /\ phi D1 = phi cc + 7) \/ (isw = false /\ phi D1 = phi cc - 2)).
  { unfold D1. destruct isw; [left; split; [reflexivity|pv]|right; split; [reflexivity|pv]]. }
  assert (Bd2 : det = true -> phi (vd2 v) < 1099511627776).
  { unfold det. intros X. apply andb_prop in X. destruct X as [_ X]. exact (ltb_true _ _ X). }
  assert (EDD : (direct = true /\ phi DD = phi D1) \/ (direct = false /\ det = true /\ phi DD = phi D1 + phi (vd2 v))).
  { unfold DD. destruct direct; [left; split; reflexivity|]. cbn [orb] in G7. rewrite G7. right. repeat split. specialize (Bd2 G7). pv. }
  assert (BD1 : 1 <= phi D1 < 1099511627776 + 8) by (destruct ED1 as [[_ X]|[_ X]]; lia).
  assert (BDD : 1 <= phi DD < 2199023255552 + 8) by (pose proof (phi_bd63 (vd2 v)); destruct EDD as [[_ X]|(_ & Hd & X)]; [lia|specialize (Bd2 Hd); lia]).
  assert (Ey : phi ylast = phi (eY b) + (phi T - 1) * phi DD).
  { unfold ylast. apply phi_of_cg; [cgs; assert (F : phi (T - 1)%uint63 = phi T - 1) by pv; unfold cg; rewrite F; reflexivity|].
    assert (0 <= (phi T - 1) * phi DD <= 2097152 * 2199023255560) by nia.
    pose proof (phi_bd63 (eY b)). lia. }
  assert (EY' : phi (ylast + DD)%uint63 = phi ylast + phi DD).
  { assert (0 <= (phi T - 1) * phi DD <= 2097152 * 2199023255560) by nia. pose proof (phi_bd63 (eY b)). pv. }
  rewrite EY' in G11.
  assert (By0 : 0 <= phi (eY b)) by (pose proof (phi_bd63 (eY b)); lia).
  assert (Byl : phi (eY b) <= phi ylast < TT) by (assert (0 <= (phi T - 1) * phi DD) by nia; lia).
  assert (El28 : phi (ylast << 28)%uint63 = phi ylast * PP) by (apply phi_lsl28; lia).
  assert (Ey28 : phi (eY b << 28)%uint63 = phi (eY b) * PP) by (apply phi_lsl28; lia).
  assert (BW0 : 0 <= phi (eW b)) by (pose proof (phi_bd63 (eW b)); lia).
  assert (Elim : phi ((e_ * eW b) >> 2)%uint63 = (phi e_ * phi (eW b)) / 4).
  { rewrite phi_lsr2. f_equal. assert (X : 0 <= phi e_ * phi (eW b) <= 3 * 1152921504606846976) by nia.
    apply phi_of_cg; [cgs|lia]. }
  set (lim := ((e_ * eW b) >> 2)%uint63) in *.
  assert (Blim : 0 <= phi lim <= 864691128455135232 /\ 4 * phi lim <= phi e_ * phi (eW b)).
  { rewrite Elim. assert (X : 0 <= phi e_ * phi (eW b) <= 3 * 1152921504606846976) by nia. Z.div_mod_to_equations. lia. }
  assert (Ehv : phi (lim + VOFF - (ylast << 28) - 8)%uint63 = phi lim + VO - phi ylast * PP - 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite El28; reflexivity|]. change (phi VOFF) with VO. nia. }
  assert (Edv : phi ((2 * eW b + 3) >> 2)%uint63 = (2 * phi (eW b) + 3) / 4).
  { rewrite phi_lsr2. f_equal. pv. }
  set (lim2 := ((2 * eW b + 3) >> 2)%uint63) in *.
  assert (Blim2 : 0 <= phi lim2 <= 576460752303423489 /\ 2 * phi (eW b) <= 4 * phi lim2).
  { rewrite Edv. Z.div_mod_to_equations. lia. }
  assert (Elv : phi (lim2 + VOFF - (eY b << 28) + 8)%uint63 = phi lim2 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Ey28; reflexivity|]. change (phi VOFF) with VO. nia. }
  assert (Eg : phi (ONE * (ylast + 64))%uint63 = PP * (phi ylast + 64)).
  { apply phi_of_cg; [cgs; unfold cg; reflexivity|lia]. }
  assert (DD4 : phi DD mod 4 = 0).
  { destruct EDD as [[Hd X]|(Hd & Hd2 & X)].
    - unfold direct in Hd. apply andb_prop in Hd. destruct Hd as [_ Hd]. apply eqb_true in Hd. rewrite phi_land3 in Hd. rewrite X. exact Hd.
    - pose proof (Bd2 Hd2) as Bx. unfold det in Hd2. apply andb_prop in Hd2. destruct Hd2 as [Hd2 _]. apply andb_prop in Hd2. destruct Hd2 as [_ Hd2].
      apply eqb_true in Hd2. rewrite phi_land3 in Hd2.
      assert (F : phi (D1 + vd2 v)%uint63 = phi D1 + phi (vd2 v)) by pv. rewrite F in Hd2. rewrite X. exact Hd2. }
  assert (Eylm : (phi ylast + phi DD) mod 4 = 0).
  { rewrite Ey. assert (Y4 : phi (eY b) = 4 * (phi (eY b) / 4)) by (Z.div_mod_to_equations; lia).
    assert (D4 : phi DD = 4 * (phi DD / 4)) by (Z.div_mod_to_equations; lia).
    rewrite Y4, D4. set (p := phi (eY b) / 4). set (q := phi DD / 4).
    replace (4 * p + (phi T - 1) * (4 * q) + 4 * q) with (0 + (p + (phi T - 1) * q + q) * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
  destruct (1048576 <=? T)%uint63 eqn:GT; [discriminate Hx|]. apply leb_false in GT. change (phi 1048576%uint63) with 1048576 in GT.
  cbv iota in Hx.
  (** numbers *)
  set (nT := Z.to_nat (phi T)).
  assert (NT : Z.of_nat nT = phi T) by (apply T_nat; exact T1).
  assert (ES1 := s1_val T ltac:(lia)). assert (ES2 := s2_val T ltac:(lia)). fold nT in ES1, ES2.
  assert (F1 : 2 * s1 nT = phi T * (phi T - 1)) by (rewrite <- NT; apply s1_form).
  set (y_ := phi (eY b)) in *. set (d_ := phi DD) in *. set (t_ := phi T) in *.
  assert (Cm : (t_ - 1) * d_ <= phi ylast) by lia.
  assert (Dd : 1 <= d_ < 1073741824) by lia.
  assert (Yy : 0 <= y_ < 1073741824) by lia.
  assert (S10 : 0 <= s1 nT).
  { assert (P : 0 <= t_ * (t_ - 1)) by (apply Z.mul_nonneg_nonneg; lia). clear - F1 P. lia. }
  assert (DS : 0 <= d_ * s1 nT <= 562949953421312).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (X : 2 * (d_ * s1 nT) = t_ * ((t_ - 1) * d_)) by (rewrite Z.mul_assoc; replace (2 * d_) with (d_ * 2) by ring; rewrite <- Z.mul_assoc, F1; ring).
    assert (X2 : t_ * ((t_ - 1) * d_) <= 1048576 * 1073741824) by (apply Z.mul_le_mono_nonneg; try lia; apply Z.mul_nonneg_nonneg; lia).
    lia. }
  assert (YT : 0 <= y_ * t_ <= 1125899906842624).
  { pose proof (mul_bd y_ t_ 1073741824 1048576 ltac:(lia) ltac:(lia)) as X. exact X. }
  assert (D1DD : 1 <= phi D1 <= d_).
  { destruct EDD as [[_ X]|(_ & _ & X)]; pose proof (phi_bd63 (vd2 v)); lia. }
  assert (Eyd : phi (eY b + D1)%uint63 = y_ + phi D1) by (unfold y_; apply phi_of_cg; [apply cg_add; apply cg_refl|lia]).
  set (yd_ := y_ + phi D1) in *.
  assert (Ydb : 0 <= yd_ < 1073741824) by (unfold yd_; lia).
  assert (YdT : 0 <= yd_ * t_ <= 1125899906842624).
  { pose proof (mul_bd yd_ t_ 1073741824 1048576 ltac:(lia) ltac:(lia)) as X. exact X. }
  assert (Et1 : phi (eY b * T + DD * (T * (T - 1) / 2))%uint63 = tsum1 y_ d_ nT).
  { unfold tsum1. rewrite NT. apply phi_of_cg; [apply cg_add; [apply cg_mul; apply cg_refl|apply cg_mul; [apply cg_refl|unfold cg; rewrite ES1; reflexivity]]|lia]. }
  assert (Edt1 : phi ((eY b + D1) * T + DD * (T * (T - 1) / 2))%uint63 = tsum1 yd_ d_ nT).
  { unfold tsum1. rewrite NT. apply phi_of_cg; [apply cg_add; [apply cg_mul; [unfold cg; rewrite Eyd; reflexivity|apply cg_refl]|apply cg_mul; [apply cg_refl|unfold cg; rewrite ES1; reflexivity]]|lia]. }
  assert (Eu : phi (eY b * T + 2 * DD * (T * (T - 1) / 2))%uint63 = y_ * t_ + 2 * (d_ * s1 nT)).
  { apply phi_of_cg; [|lia]. replace (y_ * t_ + 2 * (d_ * s1 nT)) with (y_ * t_ + 2 * d_ * s1 nT) by ring. apply cg_add; [apply cg_mul; apply cg_refl|apply cg_mul; [apply cg_mul; [reflexivity|apply cg_refl]|unfold cg; rewrite ES1; reflexivity]]. }
  assert (Eud : phi ((eY b + D1) * T + 2 * DD * (T * (T - 1) / 2))%uint63 = yd_ * t_ + 2 * (d_ * s1 nT)).
  { apply phi_of_cg; [|lia]. replace (yd_ * t_ + 2 * (d_ * s1 nT)) with (yd_ * t_ + 2 * d_ * s1 nT) by ring. apply cg_add; [apply cg_mul; [unfold cg; rewrite Eyd; reflexivity|apply cg_refl]|apply cg_mul; [apply cg_mul; [reflexivity|apply cg_refl]|unfold cg; rewrite ES1; reflexivity]]. }
  (** the moments *)
  destruct zero5_spec as [G0 V0].
  pose proof (pnat_spec ((T - 1) * T * (2 * T - 1) / 6)%uint63) as [Gs2 Vs2]. rewrite ES2 in Vs2.
  destruct (addk_spec zero5 DD _ 0 0 G0 Gs2 ltac:(fold d_; lia) ltac:(lia) ltac:(lia)) as [Gdd1 Vdd1].
  fold d_ in Vdd1. rewrite V0, Vs2 in Vdd1.
  set (dd1 := addk zero5 DD (pnat ((T - 1) * T * (2 * T - 1) / 6)%uint63)) in *.
  set (K := if isw then 378%uint63 else 274%uint63) in *.
  lazymatch type of Hx with (if ?cnd then _ else _) = _ => destruct cnd eqn:Cs end; [|discriminate Hx]. injection Hx as <-.
  apply andb_prop in Cs. destruct Cs as [Cs Lmd1]. apply andb_prop in Cs. destruct Cs as [Cs Lnd]. apply andb_prop in Cs. destruct Cs as [Cs Lap]. apply andb_prop in Cs. destruct Cs as [Cs Lm1].
  apply andb_prop in Cs. destruct Cs as [Cs Lnn]. apply andb_prop in Cs. destruct Cs as [Cs Pp]. apply andb_prop in Cs. destruct Cs as [Cs Omd2]. apply andb_prop in Cs. destruct Cs as [Cs Odt2].
  apply andb_prop in Cs. destruct Cs as [Cs Om2]. apply andb_prop in Cs. destruct Cs as [Ok1 Ot2].
  apply ltb_true in Lmd1, Lnd, Lap, Lm1, Lnn.
  change (phi 1152921504606846976%uint63) with 1152921504606846976 in Lmd1, Lap, Lm1. change (phi 1073741824%uint63) with 1073741824 in Lnd, Lnn.
  pose proof (ok5_good _ _ Gdd1 Ok1) as Gdd1'.
  destruct (addk_spec zero5 DD dd1 0 1073741824 G0 Gdd1' ltac:(fold d_; lia) ltac:(lia) ltac:(fold d_; lia)) as [Gdds Vdds].
  fold d_ in Vdds, Gdds. rewrite V0, Vdd1 in Vdds.
  set (dds := addk zero5 DD dd1) in *. clearbody dds dd1.
  pose proof (pnat_spec (eY b * T + 2 * DD * (T * (T - 1) / 2))%uint63) as [Gu Vu]. rewrite Eu in Vu.
  destruct (addk_spec dds (eY b) _ _ 0 Gdds Gu ltac:(fold y_; lia) ltac:(lia) ltac:(fold y_; lia)) as [Gt2 Vt2].
  fold y_ in Vt2, Gt2. rewrite Vdds, Vu in Vt2.
  pose proof (pnat_spec ((eY b + D1) * T + 2 * DD * (T * (T - 1) / 2))%uint63) as [Gud Vud]. rewrite Eud in Vud.
  destruct (addk_spec dds (eY b + D1)%uint63 _ _ 0 Gdds Gud ltac:(rewrite Eyd; lia) ltac:(lia) ltac:(rewrite Eyd; lia)) as [Gdt2 Vdt2].
  rewrite Eyd in Vdt2, Gdt2. rewrite Vdds, Vud in Vdt2.
  pose proof (ok5_good _ _ Gt2 Ot2) as Gt2'.
  assert (Tt2 : val5 (addk dds (eY b) (pnat (eY b * T + 2 * DD * (T * (T - 1) / 2))%uint63)) = tsum2 y_ d_ nT).
  { rewrite Vt2. unfold tsum2. rewrite NT. fold t_. ring. }
  assert (Tdt2 : val5 (addk dds (eY b + D1)%uint63 (pnat ((eY b + D1) * T + 2 * DD * (T * (T - 1) / 2))%uint63)) = tsum2 yd_ d_ nT).
  { rewrite Vdt2. unfold tsum2. rewrite NT. fold t_. ring. }
  set (t1 := (eY b * T + DD * (T * (T - 1) / 2))%uint63) in *.
  set (dt1 := ((eY b + D1) * T + DD * (T * (T - 1) / 2))%uint63) in *.
  set (t2 := addk dds (eY b) (pnat (eY b * T + 2 * DD * (T * (T - 1) / 2))%uint63)) in *.
  set (dt2 := addk dds (eY b + D1)%uint63 (pnat ((eY b + D1) * T + 2 * DD * (T * (T - 1) / 2))%uint63)) in *.
  clearbody t1 dt1 t2 dt2.
  destruct Hc as (Cn & Cm1 & Cm2 & Cap & Cnd & Cmd1 & Cmd2 & Cp).
  (** the word and the polynomial, by kind *)
  assert (BK : phi K <= 378 /\ (isw = true /\ phi K = 378 \/ isw = false /\ phi K = 274)).
  { unfold K. destruct isw; [split; [cbv; discriminate|left; split; reflexivity]|split; [cbv; discriminate|right; split; reflexivity]]. }
  destruct BK as [BK _].
  assert (Hw := word_sound b dl kind cc rae rbe D1 K z isw eq_refl eq_refl eq_refl Ecc eq_refl eq_refl eq_refl).
  assert (ED1' : isw = true /\ phi D1 = phi cc + 7 \/ isw = false /\ phi D1 = phi cc - 2) by exact ED1.
  specialize (Hw ED1').
  assert (Ev : phi rbe mod 2 = 0) by (apply eqb_true in G1; rewrite phi_land1 in G1; exact G1).
  assert (Odd : dl = false -> phi (erb b) mod 2 = 1).
  { intros Ed. rewrite Ed in G2. cbn [negb andb] in G2. apply negb_false_iff in G2. apply eqb_true in G2. rewrite phi_land1 in G2. exact G2. }
  specialize (Hw Ev Odd).
  assert (Pk : forall k, phi k + phi K < 16384 -> phi (k + K)%uint63 = phi k + phi K) by (intros k Hk; apply phi_of_cg; [apply cg_add; apply cg_refl|pose proof (phi_bd63 k); pose proof (phi_bd63 K); lia]).
  assert (Qp : exists xz zz kx kz k0 : int, word_at b dl (phi z) (phi D1) (phi xz) (phi zz) (phi kx) (phi kz) (phi k0) /\
      (if dl then stopQ 40 14 186 141 (405 + K)%uint63 (ep c) T t1 t2
       else if (kind =? 1)%uint63 then stopQ 4 2 240 72 (816 + K)%uint63 (ep c) T t1 t2
       else stopQ 4 2 384 96 (1890 + K)%uint63 (ep c) T t1 t2) = stopQ xz zz kx kz k0 (ep c) T t1 t2 /\
      phi xz < 4096 /\ phi zz < 4096 /\ phi kx < 16384 /\ phi kz < 16384 /\ phi k0 < 16384).
  { destruct Hw as [(E1 & W1)|[(E1 & E2 & W1)|(E1 & E2 & W1)]]; rewrite E1 in *.
    - exists 40%uint63, 14%uint63, 186%uint63, 141%uint63, (405 + K)%uint63. rewrite (Pk 405%uint63 ltac:(change (phi 405%uint63) with 405; lia)). change (phi 405%uint63) with 405.
      split; [exact W1|]. split; [reflexivity|]. refine (conj _ (conj _ (conj _ (conj _ _)))); first [vm_compute; reflexivity|lia].
    - exists 4%uint63, 2%uint63, 240%uint63, 72%uint63, (816 + K)%uint63. rewrite E2. rewrite (Pk 816%uint63 ltac:(change (phi 816%uint63) with 816; lia)). change (phi 816%uint63) with 816.
      split; [exact W1|]. split; [reflexivity|]. refine (conj _ (conj _ (conj _ (conj _ _)))); first [vm_compute; reflexivity|lia].
    - exists 4%uint63, 2%uint63, 384%uint63, 96%uint63, (1890 + K)%uint63. rewrite E2. rewrite (Pk 1890%uint63 ltac:(change (phi 1890%uint63) with 1890; lia)). change (phi 1890%uint63) with 1890.
      split; [exact W1|]. split; [reflexivity|]. refine (conj _ (conj _ (conj _ (conj _ _)))); first [vm_compute; reflexivity|lia]. }
  destruct Qp as (xz & zz & kx & kz & k0 & Wf & Ep & B1 & B2 & B3 & B4 & B5).
  rewrite Ep in Pp. rewrite Ep. clear Ep Hw Pk.
  (** values of the new cost *)
  assert (Bt1 : 0 <= phi t1 <= 2251799813685248) by (rewrite Et1; unfold tsum1; rewrite NT; clear - YT DS; fold t_; lia).
  assert (Bdt1 : 0 <= phi dt1 <= 2251799813685248) by (rewrite Edt1; unfold tsum1; rewrite NT; clear - YdT DS; fold t_; lia).
  assert (Enn : phi (en c + T)%uint63 = phi (en c) + t_) by (apply phi_of_cg; [apply cg_add; apply cg_refl|pose proof (phi_bd63 (en c)); clear - Cn GT T1 H0; lia]).
  assert (Em1 : phi (em1 c + t1)%uint63 = phi (em1 c) + phi t1) by (apply phi_of_cg; [apply cg_add; apply cg_refl|pose proof (phi_bd63 (em1 c)); clear - Cm1 Bt1 H0; lia]).
  assert (Eap : phi (eapps c + 2 * T)%uint63 = phi (eapps c) + 2 * t_) by (apply phi_of_cg; [apply cg_add; [apply cg_refl|apply cg_mul; [reflexivity|apply cg_refl]]|pose proof (phi_bd63 (eapps c)); clear - Cap GT T1 H0; lia]).
  destruct (add5_spec (em2 c) t2 _ _ Cm2 Gt2' ltac:(lia)) as [Gm2 Vm2]. pose proof (ok5_good _ _ Gm2 Om2) as Gm2'.
  rewrite Tt2 in Vm2.
  set (dt := if direct then 0 else 1).
  assert (Dv : (direct = true /\ dt = 0) \/ (direct = false /\ dt = 1)) by (unfold dt; destruct direct; [left|right]; split; reflexivity).
  assert (End : phi (if direct then end_ c else (end_ c + T)%uint63) = phi (end_ c) + dt * t_).
  { destruct Dv as [[-> ->]|[-> ->]]; [ring|].
    transitivity (phi (end_ c) + t_); [|ring]. apply phi_of_cg; [apply cg_add; apply cg_refl|pose proof (phi_bd63 (end_ c)); clear - Cnd GT T1 H0; lia]. }
  assert (Emd1 : phi (if direct then emd1 c else (emd1 c + dt1)%uint63) = phi (emd1 c) + dt * phi dt1).
  { destruct Dv as [[-> ->]|[-> ->]]; [ring|].
    transitivity (phi (emd1 c) + phi dt1); [|ring]. apply phi_of_cg; [apply cg_add; apply cg_refl|pose proof (phi_bd63 (emd1 c)); clear - Cmd1 Bdt1 H0; lia]. }
  assert (Emd2 : good5 1073741824 (if direct then emd2 c else add5 (emd2 c) dt2) /\ val5 (if direct then emd2 c else add5 (emd2 c) dt2) = val5 (emd2 c) + dt * tsum2 yd_ d_ nT).
  { destruct Dv as [[E1 E2]|[E1 E2]]; rewrite E2; rewrite E1 in Odt2, Omd2 |- *; cbn [orb] in Odt2.
    - split; [exact Cmd2|ring].
    - pose proof (ok5_good _ _ Gdt2 Odt2) as G2'. destruct (add5_spec (emd2 c) dt2 _ _ Cmd2 G2' ltac:(lia)) as [Ga Va].
      split; [exact (ok5_good _ _ Ga Omd2)|]. rewrite Va, Tdt2. ring. }
  destruct Emd2 as [Gmd2 Vmd2].
  set (nd := if direct then end_ c else (end_ c + T)%uint63) in *.
  set (md1 := if direct then emd1 c else (emd1 c + dt1)%uint63) in *.
  set (md2 := if direct then emd2 c else add5 (emd2 c) dt2) in *.
  assert (Spq : forall b1 S1 g1, pgood (1073741824 + GW) (stopQ xz zz kx kz k0 (ep c) T t1 t2) /\ _) by
    (intros b1 S1 g1; exact (stopQ_spec 1073741824 T t1 t2 b1 S1 g1 ltac:(lia) Gt2' xz zz kx kz k0 (ep c) Cp B1 B2 B3 B4 B5)).
  set (p := stopQ xz zz kx kz k0 (ep c) T t1 t2) in *.
  assert (Gpp : pgood 1073741824 p) by (destruct (Spq 0 0 0) as [X _]; exact (pok_good _ _ X Pp)).
  assert (Cbd : cost_bd (mkC (en c + T)%uint63 (em1 c + t1)%uint63 (add5 (em2 c) t2) (eapps c + 2 * T)%uint63 nd md1 md2 p)).
  { unfold cost_bd. cbn [en em1 em2 eapps end_ emd1 emd2 ep]. exact (conj Lnn (conj Lm1 (conj Gm2' (conj Lap (conj Lnd (conj Lmd1 (conj Gmd2 Gpp))))))). }
  assert (Main : forall (detf : bool) (dlast dres : int),
     phi (edlast b) <= phi dlast < 2147483648 ->
     (edet b = true -> detf = true /\ dres = edres b) ->
     (direct = false -> detf = true /\ phi dres = phi D1 mod 4 /\ phi ylast + phi D1 <= phi dlast) ->
     X_sem (mkX (mkEnt (ec b) (era b) (erb b) (ez b) (ed2 b) (eW b) (eW1 b) (eW2 b)
       ((if dl then mkLine (2 * Q1)%uint63 (lim2 + VOFF - (eY b << 28) + 8)%uint63 else mkLine 0%uint63 (VOFF + 16)%uint63) :: elo b)
       (mkLine (e_ * Q1)%uint63 (lim + VOFF - (ylast << 28) - 8)%uint63 :: ehi b) (ylast + DD)%uint63 ylast detf dlast dres (max_ (eGm b) (ONE * (ylast + 64))%uint63))
       (mkC (en c + T)%uint63 (em1 c + t1)%uint63 (add5 (em2 c) t2) (eapps c + 2 * T)%uint63 nd md1 md2 p))).
  { intros detf dlast dres Hdl Hd1 Hd2_ B a b0 g len p0 p1 p2 len2 d0 d1 dc HS Ha Hb Hg HG Hreg HPre HDet.
    cbn [xs xk ec era erb ez ed2 eW eW1 eW2 elo ehi eY elast edet edlast edres eGm] in *.
    rewrite phi_max, Eg in HG. destruct Hreg as (RL & RU & R1 & R2).
    apply Forall_cons_iff in RL. destruct RL as [Rlo RL]. apply Forall_cons_iff in RU. destruct RU as [Rhi RU].
    set (S := a + b0) in *.
    assert (HR : Reach (phi (ez b)) B (phi (ez b)) (B + y_) (totn c len len2) (totr c p0 p1 p2 d0 d1 dc b0 S g)).
    { pose proof (XS B a b0 g len p0 p1 p2 len2 d0 d1 dc) as XR. cbn [xs xk] in XR. apply XR; try assumption.
      - clear - HG. lia.
      - unfold reg. exact (conj RL (conj RU (conj R1 R2))).
      - eapply XPre_mono; [|exact HPre]. clear - BL2 Byl. lia.
      - intros E1. destruct (Hd1 E1) as [E2 ->]. specialize (HDet E2). intros y Hy Hm. apply HDet; [clear - Hy Hdl; lia|exact Hm]. }
    assert (Hhi : 32 * g <= PP * (phi e_ * S - 4 * (b0 + g * phi ylast))).
    { unfold hi_l in Rhi. cbn [lt lv] in Rhi. rewrite Ehv in Rhi.
      assert (Q : phi (e_ * Q1)%uint63 = phi e_ * 268435456) by (destruct Ee as [X|X]; pv). rewrite Q in Rhi.
      apply (line_hi1 (phi e_) (phi (eW b)) (phi ylast) b0 S g (phi lim)); [|exact Hg|clear - Blim; lia].
      replace (phi lim - phi ylast * PP - 8) with (phi lim + VO - phi ylast * PP - 8 - VO) by ring. exact Rhi. }
    set (n0 := len + 2 + dt * len2).
    assert (Round : forall t, 0 <= t < Z.of_nat nT ->
       Reach (phi (ez b)) (B + y_ + t * d_) (phi (ez b)) (B + y_ + (t + 1) * d_) n0
       (p0 + p1 * (y_ + t * d_) + p2 * ((y_ + t * d_) * (y_ + t * d_)) + qcost (phi xz) (phi zz) (phi kx) (phi kz) (phi k0) (b0 + g * (y_ + t * d_)) (S + (y_ + t * d_))
        + dt * (d0 + d1 * (y_ + t * d_ + phi D1) + dc * ((y_ + t * d_ + phi D1) * (y_ + t * d_ + phi D1))))).
    { intros t Ht. rewrite NT in Ht. set (yt := y_ + t * d_).
      assert (Yt : y_ <= yt <= phi ylast).
      { unfold yt. rewrite Ey. assert (0 <= t * d_) by (apply Z.mul_nonneg_nonneg; lia). assert (t * d_ <= (t_ - 1) * d_) by (apply Z.mul_le_mono_nonneg_r; lia). clear - H0 H1. lia. }
      assert (Yt4 : yt mod 4 = 0).
      { unfold yt. assert (Y4 : y_ = 4 * (y_ / 4)) by (clear - BY4; Z.div_mod_to_equations; lia).
        assert (D4 : d_ = 4 * (d_ / 4)) by (clear - DD4; Z.div_mod_to_equations; lia).
        rewrite Y4, D4. set (p9 := y_ / 4). set (q9 := d_ / 4).
        replace (4 * p9 + t * (4 * q9)) with (0 + (p9 + t * q9) * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
      assert (HP : Reach (phi (ez b)) (B + yt) (a - (g - 1) * yt) (b0 + g * yt) len (p0 + p1 * yt + p2 * (yt * yt))) by (apply HPre; [clear - Yt By0 BL2; lia|exact Yt4]).
      set (at_ := a - (g - 1) * yt) in *. set (bt := b0 + g * yt) in *.
      assert (Ab : at_ + bt = S + yt) by (unfold at_, bt, S; ring).
      assert (Sum_ : at_ + bt = B + yt + phi (ec b)) by (rewrite Ab, HS; ring).
      assert (Ra : phi (era b) = at_ mod 4) by (unfold at_; rewrite res_at by exact Yt4; symmetry; exact Ha).
      assert (Rb : phi (erb b) = bt mod 4) by (unfold bt; rewrite resb_at by exact Yt4; symmetry; exact Hb).
      assert (GnH : PP * (phi ylast + 64) <= g) by (clear - HG; lia).
      assert (Gd : if dl then at_ + 3 < bt /\ 4 * bt < 3 * (at_ + bt) + 12 else 5 <= bt /\ bt + 1 <= at_ /\ 4 * bt < at_ + bt + 18).
      { destruct dl.
        - assert (HL : 32 * g <= PP * (4 * (b0 + g * y_) - 2 * S)).
          { unfold lo_l in Rlo. cbn [lt lv] in Rlo. rewrite Elv in Rlo.
            apply (line_lo1 2 (phi (eW b)) y_ b0 S g (phi lim2)); [|exact Hg|clear - Blim2; lia].
            change (2 * 268435456) with (phi (2 * Q1)%uint63).
            replace (phi lim2 - y_ * PP + 8) with (phi lim2 + VO - y_ * PP + 8 - VO) by ring. exact Rlo. }
          assert (E3 : phi e_ = 3) by reflexivity. rewrite E3 in Hhi.
          destruct (guards_D a b0 g S y_ yt (phi ylast) eq_refl Hg GnH ltac:(clear - Yt; lia) ltac:(clear - By0; lia) Hhi HL) as [Gd1 Gd2].
          fold at_ bt in Gd1, Gd2. exact (conj Gd1 Gd2).
        - assert (L0 : 16 * g <= PP * b0).
          { unfold lo_l in Rlo. cbn [lt lv] in Rlo. change (phi 0%uint63) with 0 in Rlo. change (phi (VOFF + 16)%uint63 - VO) with 16 in Rlo.
            unfold lo_z in Rlo. clear - Rlo. lia. }
          assert (E1_ : phi e_ = 1) by reflexivity. rewrite E1_ in Hhi.
          destruct (guards_UV a b0 g S yt (phi ylast) eq_refl Hg GnH ltac:(clear - Yt By0; lia) ltac:(clear - Hhi; lia) L0) as (Gu1 & Gu2 & Gu3).
          fold at_ bt in Gu1, Gu2, Gu3. exact (conj Gu1 (conj Gu2 Gu3)). }
      pose proof (Wf (B + yt) at_ bt Sum_ Ra Rb Gd) as Wd.
      rewrite Ab in Wd. fold at_ bt in Wd.
      pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ HP Wd) as Rt1.
      destruct Dv as [[Hd Dt0]|[Hd Dt1]].
      - assert (Zz : z = ez b).
        { unfold direct in Hd. apply andb_prop in Hd. destruct Hd as [Hd _]. apply Uint63.eqb_spec in Hd. rewrite Hd, <- G5. reflexivity. }
        assert (Dq : phi D1 = d_) by (destruct EDD as [[_ X]|(X & _)]; [symmetry; exact X|rewrite Hd in X; discriminate X]).
        rewrite Zz, Dq in Rt1.
        replace (B + y_ + t * d_) with (B + yt) by (unfold yt; ring).
        replace (B + y_ + (t + 1) * d_) with (B + yt + d_) by (unfold yt; ring).
        eapply Rconv; [exact Rt1|unfold n0; rewrite Dt0; ring|rewrite Dt0; ring].
      - destruct EDD as [[X _]|(_ & Hd2 & X)]; [rewrite Hd in X; discriminate X|].
        destruct (Hd2_ Hd) as (D1_ & D2_ & D3_). specialize (HDet D1_).
        assert (Zz : phi z = 28 - phi (ez b)).
        { pose proof Hd2 as Hd3. unfold det in Hd3. apply andb_prop in Hd3. destruct Hd3 as [Hd3 _]. apply andb_prop in Hd3. destruct Hd3 as [Hd3 _]. apply andb_prop in Hd3. destruct Hd3 as [_ Hd3].
          apply eqb_true in Hd3. rewrite G5. assert (F : phi (z + vz v)%uint63 = phi z + phi (vz v)).
          { assert (Hz' : phi z <= 22) by (unfold z; destruct isw; cbv; discriminate). destruct Hz as [Hv|Hv]; pv. }
          rewrite F in Hd3. change (phi 28%uint63) with 28 in Hd3. clear - Hd3. lia. }
        assert (M4 : (yt + phi D1) mod 4 = phi D1 mod 4) by (rewrite Z.add_mod by lia; rewrite Yt4; rewrite Z.add_0_l, Z.mod_mod by lia; reflexivity).
        pose proof (HDet (yt + phi D1) ltac:(clear - Yt By0 D3_ D1DD BL2; lia) ltac:(rewrite M4; symmetry; exact D2_)) as HD.
        rewrite <- Zz in HD.
        replace (B + (yt + phi D1)) with (B + yt + phi D1) in HD by ring.
        pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ Rt1 HD) as Rt2.
        replace (B + y_ + t * d_) with (B + yt) by (unfold yt; ring).
        assert (Eq : d_ = phi D1 + phi (ed2 b)) by (rewrite G6; exact X).
        assert (Eq2 : B + y_ + (t + 1) * d_ = B + yt + phi D1 + phi (ed2 b)) by (unfold yt; rewrite Eq; ring).
        rewrite Eq2.
        eapply Rconv; [exact Rt2|unfold n0; rewrite Dt1; ring|rewrite Dt1; ring]. }
    pose proof (stop_sum (phi (ez b)) B y_ d_ nT n0 p0 p1 p2 (phi xz) (phi zz) (phi kx) (phi kz) (phi k0) b0 S g dt d0 d1 dc (phi D1) Round) as RR.
    change (y_ + phi D1) with yd_ in RR. rewrite NT in RR.
    pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ HR RR) as Rtot.
    rewrite EY', Ey.
    replace (B + (y_ + (t_ - 1) * d_ + d_)) with (B + y_ + t_ * d_) by ring.
    eapply Rconv; [exact Rtot| |].
    - unfold totn, n0. cbn [en eapps end_]. rewrite Enn, Eap, End. ring.
    - destruct (Spq b0 S g) as [_ Vp]. unfold totr. cbn [en em1 em2 end_ emd1 emd2 ep]. rewrite Vp, Enn, Em1, Vm2, End, Emd1, Vmd2, Et1, Edt1, Tt2.
      apply stop_r_eq. }
  destruct direct eqn:Dr.
  - injection H as <-. split; [split; [exact Oks|split; [exact Cbd|]]|exact Facts].
    apply Main; [clear - BD; lia|intros X; split; [exact X|reflexivity]|intros X; discriminate X].
  - destruct (negb (edet b) || (edres b =? (D1 land 3))%uint63) eqn:Cd; [|discriminate H].
    injection H as <-. split; [split; [exact Oks|split; [exact Cbd|]]|exact Facts].
    assert (EyD : phi (ylast + D1)%uint63 = phi ylast + phi D1) by (apply phi_of_cg; [apply cg_add; apply cg_refl|clear - Byl Yy D1DD Dd; lia]).
    apply Main.
    + rewrite phi_max, EyD. clear - BD Byl Yy D1DD Dd G11. lia.
    + intros E1. rewrite E1 in Cd. cbn [negb orb] in Cd. apply Uint63.eqb_spec in Cd. split; [reflexivity|symmetry; exact Cd].
    + intros _. split; [reflexivity|]. rewrite phi_land3. split; [reflexivity|]. rewrite phi_max, EyD. clear. lia.
Qed.
