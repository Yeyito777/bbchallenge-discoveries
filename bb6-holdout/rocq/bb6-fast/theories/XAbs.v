(** Exact costs through a pair of letters and a child block. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
Import ListNotations.
From BB6 Require Import Map Walk Num.
From BF Require Import Ints HLines HCore HAbs XCost XCore.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Definition x_absorb (bx chx : XEnt) (dl : bool) : option XEnt :=
  let b := xs bx in let ch := xs chx in let cb := xk bx in let cc := xk chx in
  match absorb b ch dl with
  | None => None
  | Some s =>
    let y := eY b in
    let kind := if dl then 0%uint63 else kind_of (era b) (erb b) in
    let n := en cc in
    let q1 := if dl then XCost.pairDD (digitDD (ep cc)) n (em1 cc) (em2 cc)
              else if (kind =? 1)%uint63 then pairUV 100 41 299 (digitUD (ep cc)) n (em1 cc) (em2 cc)
              else pairUV 116 49 581 (digitVD (ep cc)) n (em1 cc) (em2 cc) in
    if pok q1 then
      match (if (y =? 0)%uint63 then Some q1 else shift y q1) with
      | None => None
      | Some s1 =>
        let p := padd (ep cb) s1 in
        let m1 := (em1 cc + n * y)%uint63 in
        let m2 := addk (em2 cc) y (pnat (2 * em1 cc + n * y)%uint63) in
        let ndc := end_ cc in
        let md1 := (emd1 cc + ndc * y)%uint63 in
        let md2 := addk (emd2 cc) y (pnat (2 * emd1 cc + ndc * y)%uint63) in
        let nm2 := add5 (em2 cb) m2 in let nmd2 := add5 (emd2 cb) md2 in
        let nn := (en cb + n)%uint63 in let nm1 := (em1 cb + m1)%uint63 in let nap := (eapps cb + eapps cc + 2 * n)%uint63 in
        let nnd := (end_ cb + ndc)%uint63 in let nmd1 := (emd1 cb + md1)%uint63 in
        if pok s1 && pok p && ok5 m2 && ok5 md2 && ok5 nm2 && ok5 nmd2 && (nn <? 1073741824)%uint63 && (nm1 <? 1152921504606846976)%uint63
           && (nap <? 1152921504606846976)%uint63 && (nnd <? 1073741824)%uint63 && (nmd1 <? 1152921504606846976)%uint63 then
          Some (mkX s (mkC nn nm1 nm2 nap nnd nmd1 nmd2 p))
        else None
      end
    else None
  end.

Definition hide (P : Prop) : Prop := P.

Ltac atomize :=
  repeat match goal with
  | |- context [pval ?p ?x ?y ?z] => generalize (pval p x y z); intro
  | |- context [val5 ?x] => generalize (val5 x); intro
  | |- context [Uint63.to_Z ?x] => generalize (Uint63.to_Z x); intro
  end.

Lemma shift_or y q1 s1 : pgood 1073741824 q1 -> phi y < 1073741824 -> (if (y =? 0)%uint63 then Some q1 else shift y q1) = Some s1 ->
  pgood H61 s1 /\ forall b S g, pval s1 b S g = pval q1 (b + g * phi y) (S + phi y) g.
Proof.
  intros G Hy H. destruct (y =? 0)%uint63 eqn:C.
  - injection H as <-. apply eqb_true in C. change (phi 0%uint63) with 0 in C. rewrite C. split.
    + destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
      assert (M : forall x, good5 1073741824 x -> good5 H61 x) by (intros x; apply good_mono; lia).
      exact (conj (M _ G1) (conj (M _ G2) (conj (M _ G3) (conj (M _ G4) (conj (M _ G5) (conj (M _ G6) (conj (M _ G7) (conj (M _ G8) (conj (M _ G9) (M _ G10)))))))))).
    + intros b S g. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity.
  - split; [exact (proj1 (shift_spec y q1 s1 0 0 0 G Hy H))|]. intros b S g. exact (proj2 (shift_spec y q1 s1 b S g G Hy H)).
Qed.

Lemma absorb_n_eq n1 l1 d1 N A0 ND a1 len len2 :
  n1 * len + l1 + d1 * len2 + (N * (len + 2) + A0 + ND * len2) = (n1 + N) * len + (l1 + A0 + 2 * N) + (d1 + ND) * len2 + 0 * a1.
Proof. ring. Qed.

Lemma absorb_r_eq En Em1 Em2 PVb End Emd1 Emd2 N M1 M2 PVc ND MD1 MD2 p0 p1 p2 d0 d1 dc y X0 Z0 g ax kx kz k0 :
  p0 * En + p1 * Em1 + p2 * Em2 + PVb + d0 * End + d1 * Emd1 + dc * Emd2 +
  ((p0 + p1 * y + p2 * (y * y) + (ax * (X0 * Z0) + kx * X0 - kz * Z0 - k0)) * N
   + (p1 + 2 * p2 * y + ax * (X0 + g * Z0) + kx * g - kz) * M1 + (p2 + ax * g) * M2 + PVc
   + (d0 + d1 * y + dc * (y * y)) * ND + (d1 + 2 * dc * y) * MD1 + dc * MD2) =
  p0 * (En + N) + p1 * (Em1 + (M1 + N * y)) + p2 * (Em2 + (M2 + y * (2 * M1 + N * y)))
  + (PVb + (PVc + ax * (N * (X0 * Z0) + M1 * (X0 + g * Z0) + M2 * g) + kx * (N * X0 + M1 * g) - kz * (N * Z0 + M1) - k0 * N))
  + d0 * (End + ND) + d1 * (Emd1 + (MD1 + ND * y)) + dc * (Emd2 + (MD2 + y * (2 * MD1 + ND * y))).
Proof. ring. Qed.

Lemma pq_DD P n m1 m2 : pgood 1073741824 P ->
  pgood (GD + GW) (XCost.pairDD (digitDD P) n m1 m2) /\ forall X W0 g0, pval (XCost.pairDD (digitDD P) n m1 m2) X W0 g0 = pval P (4 * X - 3 * W0 - 12) (W0 + 6) (4 * g0 - 3)
    + 0 * (phi n * (X * W0) + phi m1 * (X + g0 * W0) + val5 m2 * g0) + 90 * (phi n * X + phi m1 * g0) - 90 * (phi n * W0 + phi m1) - 144 * phi n.
Proof.
  intros GP. destruct (digitDD_spec P 0 0 0 GP) as [Gq _].
  destruct (XCost.pairDD_spec GD n m1 m2 0 0 0 ltac:(unfold GD; lia) _ Gq) as [G1' _]. split; [exact G1'|].
  intros X W0 g0. destruct (digitDD_spec P X W0 g0 GP) as [_ V1].
  destruct (XCost.pairDD_spec GD n m1 m2 X W0 g0 ltac:(unfold GD; lia) _ Gq) as [_ V2]. rewrite V2, V1.
  generalize (pval P (4 * X - 3 * W0 - 12) (W0 + 6) (4 * g0 - 3)) (phi n) (phi m1) (val5 m2). intros. ring.
Qed.
Lemma pq_UD P n m1 m2 : pgood 1073741824 P -> good5 1073741824 m2 ->
  pgood (GD + GW) (pairUV 100 41 299 (digitUD P) n m1 m2) /\ forall X W0 g0, pval (pairUV 100 41 299 (digitUD P) n m1 m2) X W0 g0 = pval P (4 * X - 1 * W0 - 18) (W0 + 10) (4 * g0 - 1)
    + 4 * (phi n * (X * W0) + phi m1 * (X + g0 * W0) + val5 m2 * g0) + 100 * (phi n * X + phi m1 * g0) - 41 * (phi n * W0 + phi m1) - 299 * phi n.
Proof.
  intros GP Gm2. destruct (digitUD_spec P 0 0 0 GP) as [Gq _].
  destruct (pairUV_spec GD n m1 m2 0 0 0 ltac:(unfold GD; lia) Gm2 100 41 299 _ Gq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [G1' _]. split; [exact G1'|].
  intros X W0 g0. destruct (digitUD_spec P X W0 g0 GP) as [_ V1].
  destruct (pairUV_spec GD n m1 m2 X W0 g0 ltac:(unfold GD; lia) Gm2 100 41 299 _ Gq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [_ V2].
  rewrite V2, V1. change (phi 100%uint63) with 100. change (phi 41%uint63) with 41. change (phi 299%uint63) with 299. replace (4 * X - W0 - 18) with (4 * X - 1 * W0 - 18) by ring.
  generalize (pval P (4 * X - 1 * W0 - 18) (W0 + 10) (4 * g0 - 1)) (phi n) (phi m1) (val5 m2). intros. ring.
Qed.
Lemma pq_VD P n m1 m2 : pgood 1073741824 P -> good5 1073741824 m2 ->
  pgood (GD + GW) (pairUV 116 49 581 (digitVD P) n m1 m2) /\ forall X W0 g0, pval (pairUV 116 49 581 (digitVD P) n m1 m2) X W0 g0 = pval P (4 * X - 1 * W0 - 30) (W0 + 14) (4 * g0 - 1)
    + 4 * (phi n * (X * W0) + phi m1 * (X + g0 * W0) + val5 m2 * g0) + 116 * (phi n * X + phi m1 * g0) - 49 * (phi n * W0 + phi m1) - 581 * phi n.
Proof.
  intros GP Gm2. destruct (digitVD_spec P 0 0 0 GP) as [Gq _].
  destruct (pairUV_spec GD n m1 m2 0 0 0 ltac:(unfold GD; lia) Gm2 116 49 581 _ Gq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [G1' _]. split; [exact G1'|].
  intros X W0 g0. destruct (digitVD_spec P X W0 g0 GP) as [_ V1].
  destruct (pairUV_spec GD n m1 m2 X W0 g0 ltac:(unfold GD; lia) Gm2 116 49 581 _ Gq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [_ V2].
  rewrite V2, V1. change (phi 116%uint63) with 116. change (phi 49%uint63) with 49. change (phi 581%uint63) with 581. replace (4 * X - W0 - 30) with (4 * X - 1 * W0 - 30) by ring.
  generalize (pval P (4 * X - 1 * W0 - 30) (W0 + 14) (4 * g0 - 1)) (phi n) (phi m1) (val5 m2). intros. ring.
Qed.

Lemma x_absorb_sound bx chx dl xr : x_ok bx -> x_ok chx -> x_absorb bx chx dl = Some xr ->
  x_ok xr /\ ec (xs xr) = ec (xs bx) /\ era (xs xr) = era (xs bx) /\ erb (xs xr) = erb (xs bx) /\ ez (xs xr) = ez (xs bx) /\ ed2 (xs xr) = ed2 (xs bx) /\ eW (xs xr) = eW (xs bx).
Proof.
  destruct bx as [b cb]. destruct chx as [ch cc]. intros [Hok [Hcb XSb]] [HokC [Hcc XSc]] HX. unfold x_absorb in HX. cbn [xs xk] in *. cbv zeta in HX.
  destruct (absorb b ch dl) as [s|] eqn:H; [|discriminate HX].
  destruct (absorb_sound _ _ _ _ Hok HokC H) as [Oks Facts].
  destruct Hok as [Bd _]. destruct HokC as [BdC _]. unfold absorb in H. cbv zeta in H.
  destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  destruct BdC as (CL & CU & CW & CW1 & CW2 & CY & CY4 & CL2 & Cc & CD & CG & CWa & CWb).
  assert (BY4' : exists k, phi (eY b) = 4 * k) by (exists (phi (eY b) / 4); pose proof (div4 (phi (eY b))); clear -H0 BY4; Z.div_mod_to_equations; lia).
  assert (CY4' : exists k, phi (eY ch) = 4 * k) by (exists (phi (eY ch) / 4); pose proof (div4 (phi (eY ch))); clear -H0 CY4; Z.div_mod_to_equations; lia).
  destruct BY4' as [ky Ky]. destruct CY4' as [kc Kc]. clear BY4 CY4.
  set (kind := if dl then 0%uint63 else kind_of (era b) (erb b)) in *.
  set (e_ := if dl then 3%uint63 else 1%uint63) in *.
  set (K2 := if dl then 6%uint63 else if (kind =? 1)%uint63 then 10%uint63 else 14%uint63) in *.
  set (ra1 := ra_next (era b) (erb b) kind) in *.
  set (rb1 := rb_next (era b) (erb b) kind) in *.
  set (Wq := (eW b >> 2)%uint63) in *.
  set (yfx := (eY b << 28)%uint63) in *.
  set (Y' := (eY b + eY ch)%uint63) in *.
  destruct ((ec ch =? ec b + K2)%uint63 && (era ch =? ra_next ra1 rb1 0)%uint63 && (erb ch =? rb_next ra1 rb1 0)%uint63
     && (ez ch =? ez b)%uint63 && (ed2 ch =? ed2 b)%uint63 && (dl || ((erb b land 1) =? 1)%uint63)
     && (eW ch =? eW1 ch)%uint63 && (eW ch <=? Wq)%uint63 && ((Wq - eW ch) <? 4294967296)%uint63 && (Y' <? 1073741824)%uint63 && (16 <=? eW2 ch)%uint63) eqn:G; [|discriminate].
  repeat (apply andb_prop in G; destruct G as [G ?]).
  rename G into G1. rename H0 into G11. rename H1 into G10. rename H2 into G9. rename H3 into G8. rename H4 into G7.
  rename H5 into G6. rename H6 into G5. rename H7 into G4. rename H8 into G3. rename H9 into G2.
  apply Uint63.eqb_spec in G1, G2, G3, G4, G5, G7.
  apply leb_true in G8. apply ltb_true in G9. apply ltb_true in G10. apply leb_true in G11.
  change (phi 4294967296%uint63) with 4294967296 in G9. change (phi 1073741824%uint63) with TT in G10. change (phi 16%uint63) with 16 in G11.
  assert (Ee : (dl = true /\ phi e_ = 3) \/ (dl = false /\ phi e_ = 1)) by (unfold e_; destruct dl; [left|right]; split; reflexivity).
  assert (Ee' : phi e_ = 1 \/ phi e_ = 3) by (destruct Ee as [[_ X]|[_ X]]; [right|left]; exact X).
  assert (BW0 : 0 <= phi (eW b)) by (pose proof (phi_bd63 (eW b)); clear H; lia).
  assert (BWq : 0 <= phi Wq <= 288230376151711744 /\ 4 * phi Wq <= phi (eW b) <= 4 * phi Wq + 3).
  { assert (EWq : phi Wq = phi (eW b) / 4) by (unfold Wq; apply phi_lsr2). pose proof (div4 (phi (eW b))) as D. rewrite <- EWq in D. clear EWq. pose proof (phi_bd63 Wq). lia. }
  assert (BY0 : 0 <= phi (eY b)) by (pose proof (phi_bd63 (eY b)); lia).
  assert (CY0 : 0 <= phi (eY ch)) by (pose proof (phi_bd63 (eY ch)); lia).
  assert (CL0 : 0 <= phi (elast ch)) by (pose proof (phi_bd63 (elast ch)); lia).
  assert (Eyf : phi yfx = phi (eY b) * PP) by (unfold yfx; apply phi_lsl28; lia).
  assert (EY' : phi Y' = phi (eY b) + phi (eY ch)) by (unfold Y'; pv).
  rewrite EY' in G10.
  assert (ElY : phi (eY b + elast ch)%uint63 = phi (eY b) + phi (elast ch)) by pv.
  assert (El28 : phi ((eY b + elast ch) << 28)%uint63 = (phi (eY b) + phi (elast ch)) * PP) by (rewrite <- ElY; apply phi_lsl28; lia).
  (** the lines of the pair *)
  set (l1 := ((eW b + 3) >> 2)%uint63) in *. set (l3 := ((3 * eW b + 3) >> 2)%uint63) in *. set (l2 := (eW b >> 1)%uint63) in *.
  assert (Bl1 : 0 <= phi l1 <= 288230376151711745 /\ phi (eW b) <= 4 * phi l1).
  { assert (Lim1 : phi l1 = (phi (eW b) + 3) / 4) by (unfold l1; rewrite phi_lsr2; f_equal; pv).
    pose proof (div4 (phi (eW b) + 3)) as D. rewrite <- Lim1 in D. clear Lim1. pose proof (phi_bd63 l1). lia. }
  assert (Bl3 : 0 <= phi l3 <= 864691128455135233 /\ 3 * phi (eW b) <= 4 * phi l3).
  { assert (Lim3 : phi l3 = (3 * phi (eW b) + 3) / 4) by (unfold l3; rewrite phi_lsr2; f_equal; pv).
    pose proof (div4 (3 * phi (eW b) + 3)) as D. rewrite <- Lim3 in D. clear Lim3. pose proof (phi_bd63 l3). lia. }
  assert (Bl2 : 0 <= phi l2 <= 576460752303423488 /\ 4 * phi l2 <= 2 * phi (eW b)).
  { assert (Lim2 : phi l2 = phi (eW b) / 2) by (unfold l2; rewrite lsr_spec; reflexivity).
    pose proof (div2 (phi (eW b))) as D. rewrite <- Lim2 in D. clear Lim2. pose proof (phi_bd63 l2). lia. }
  assert (El1v : phi (l1 + VOFF - yfx + 8)%uint63 = phi l1 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Eyf; reflexivity|lia]. }
  assert (El3v : phi (l3 + VOFF - yfx + 8)%uint63 = phi l3 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Eyf; reflexivity|lia]. }
  assert (El2v : phi (l2 + VOFF - ((eY b + elast ch) << 28) - 8)%uint63 = phi l2 + VO - (phi (eY b) + phi (elast ch)) * PP - 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite El28; reflexivity|lia]. }
  destruct (pulls true e_ Wq (eW ch) yfx (elo ch) _) as [lo|] eqn:PL; [|discriminate].
  destruct (pulls false e_ Wq (eW ch) yfx (ehi ch) _) as [hi|] eqn:PU; [|discriminate].
  destruct (pulls_spec _ _ _ _ _ _ _ _ PL) as (PL1 & PL2 & PL3).
  destruct (pulls_spec _ _ _ _ _ _ _ _ PU) as (PU1 & PU2 & PU3).
  destruct (maxv_spec (ehi ch) 0%uint63) as [Mv1 Mv2].
  destruct (maxv_spec (elo ch) (maxv (ehi ch) 0%uint63)) as [Mv3 Mv4].
  set (vm := maxv (elo ch) (maxv (ehi ch) 0%uint63)) in *.
  assert (Bvm : 0 <= phi vm) by (pose proof (phi_bd63 vm); lia).
  assert (Ec5 : (ec ch = (ec b + K2)%uint63)) by exact G1.
  set (gneed := (ONE * (eY b + 64) + vm + eW ch + eW2 ch)%uint63) in *.
  set (Gm := max_ (max_ (eGm b) gneed) ((eGm ch >> 2) + 2)%uint63) in *.
  set (dlast1 := (eY b + edlast ch)%uint63) in *.
  destruct ((gneed <? 2305843009213693952)%uint63 && (Gm <? 2305843009213693952)%uint63 && (dlast1 <? 2147483648)%uint63
         && (negb (edet ch) || negb (edet b) || (edres b =? edres ch)%uint63)) eqn:G12; [|discriminate].
  repeat (apply andb_prop in G12; destruct G12 as [G12 ?]).
  rename G12 into G13. rename H0 into G16. rename H1 into G15. rename H2 into G14.
  apply ltb_true in G13, G14, G15.
  change (phi 2305843009213693952%uint63) with 2305843009213693952 in G13, G14. change (phi 2147483648%uint63) with 2147483648 in G15.
  assert (Egn : phi gneed = PP * (phi (eY b) + 64) + phi vm + phi (eW ch) + phi (eW2 ch)).
  { assert (Mub : phi vm <= 2305843009213693952).
    { unfold vm. apply maxv_ub; [exact CL|apply maxv_ub; [exact CU|vm_compute; intro X0; discriminate X0]]. }
    unfold gneed. apply phi_of_cg; [cgs; unfold cg; reflexivity|]. pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia. }
  assert (EdlL : phi dlast1 = phi (eY b) + phi (edlast ch)) by (unfold dlast1; pv).
  assert (BG0 : 0 <= phi (eGm ch)) by (pose proof (phi_bd63 (eGm ch)); lia).
  assert (GcD : 4 * phi (eGm ch >> 2)%uint63 <= phi (eGm ch) < 4 * phi (eGm ch >> 2)%uint63 + 4 /\ 0 <= phi (eGm ch >> 2)%uint63 < 2305843009213693952).
  { assert (Ee4 : phi (eGm ch >> 2)%uint63 = phi (eGm ch) / 4) by apply phi_lsr2. pose proof (div4 (phi (eGm ch))) as D. rewrite <- Ee4 in D. clear Ee4. pose proof (phi_bd63 (eGm ch >> 2)%uint63). lia. }
  assert (EGm : phi Gm = Z.max (Z.max (phi (eGm b)) (phi gneed)) (phi (eGm ch >> 2)%uint63 + 2)).
  { unfold Gm. rewrite !phi_max. f_equal. pv. }
  assert (EW14 : phi (4 * eW1 ch)%uint63 = 4 * phi (eW1 ch)) by pv.
  assert (EW24 : phi (4 * eW2 ch - 64)%uint63 = 4 * phi (eW2 ch) - 64) by pv.
  assert (G9' : phi Wq - phi (eW ch) < 4294967296) by (assert (Dm : phi (Wq - eW ch)%uint63 = phi Wq - phi (eW ch)) by pv; lia).
  assert (EWc : phi (eW ch) = phi (eW1 ch)) by (rewrite G7; reflexivity).
  (** the pair of letters *)
  assert (Pr : exists eZ KZ K2Z ax kx kz k0, phi e_ = eZ /\ phi K2 = K2Z /\ 0 <= KZ <= 30 /\ 0 <= K2Z <= 14 /\ (eZ = 1 \/ eZ = 3) /\
     (forall at_ bt, phi (era b) = at_ mod 4 -> phi (erb b) = bt mod 4 ->
       (if dl then at_ + 3 < bt /\ (2 * at_ + 6) + 3 < bt - at_ - 3
        else bt mod 2 = 1 /\ 5 <= bt /\ bt + 1 <= at_ /\ 4 * bt > at_ + bt + 30) ->
       Reach at_ bt (st_a eZ KZ K2Z at_ bt) (st_b eZ KZ at_ bt) 2 (ax * (bt * (at_ + bt)) + kx * bt - kz * (at_ + bt) - k0) /\
       phi (ra_next ra1 rb1 0) = st_a eZ KZ K2Z at_ bt mod 4 /\ phi (rb_next ra1 rb1 0) = st_b eZ KZ at_ bt mod 4) /\
     (forall P n m1 m2, pgood 1073741824 P -> good5 1073741824 m2 ->
       let q1 := (if dl then XCost.pairDD (digitDD P) n m1 m2
                  else if (kind =? 1)%uint63 then pairUV 100 41 299 (digitUD P) n m1 m2
                  else pairUV 116 49 581 (digitVD P) n m1 m2) in
       pgood (GD + GW) q1 /\ forall X W0 g0, pval q1 X W0 g0 = pval P (4 * X - eZ * W0 - KZ) (W0 + K2Z) (4 * g0 - eZ)
         + ax * (phi n * (X * W0) + phi m1 * (X + g0 * W0) + val5 m2 * g0)
         + kx * (phi n * X + phi m1 * g0) - kz * (phi n * W0 + phi m1) - k0 * phi n)).
  { destruct dl.
    - exists 3, 12, 6, 0, 90, 90, 144. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
      + intros at_ bt Ra Rb [Gg1 Gg2]. destruct (HAbs.pairDD at_ bt _ _ Ra Rb Gg1 Gg2) as (_ & Pa & Pb). split; [|split; [exact Pa|exact Pb]].
        pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ (XD _ _ Gg1) (XD _ _ Gg2)) as R.
        unfold st_a, st_b. replace (at_ + bt + 6 - (4 * bt - 3 * (at_ + bt) - 12)) with (2 * (2 * at_ + 6) + 6) by ring.
        replace (4 * bt - 3 * (at_ + bt) - 12) with (bt - at_ - 3 - (2 * at_ + 6) - 3) by ring.
        eapply Rconv; [exact R|ring|ring].
      + intros P n m1 m2 GP Gm2. exact (pq_DD P n m1 m2 GP).
    - destruct (Z.eq_dec (phi kind) 1) as [Kk|Kk].
      + assert (Kk' : kind = 1%uint63) by (apply to_Z_inj; exact Kk).
        exists 1, 18, 10, 4, 100, 41, 299. split; [reflexivity|]. split; [unfold K2; rewrite Kk'; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros at_ bt Ra Rb (Gg1 & Gg2 & Gg3 & Gg4).
          destruct (res_kind (era b) (erb b) at_ bt Ra Rb) as [[_ K5]|[K4 _]]; [|exfalso; change (kind_of (era b) (erb b)) with kind in K4; lia].
          destruct (pairU at_ bt _ _ Ra Rb Gg1 Gg2 Gg3 Gg4 K5) as (_ & Pa & Pb). unfold ra1, rb1. rewrite Kk'. split; [|split; [exact Pa|exact Pb]].
          assert (Gd2 : (at_ - bt + 11) + 3 < 2 * bt - 4) by lia.
          pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ (XU _ _ Gg1 K5 Gg2 Gg3) (XD _ _ Gd2)) as R.
          unfold st_a, st_b. replace (at_ + bt + 10 - (4 * bt - 1 * (at_ + bt) - 18)) with (2 * (at_ - bt + 11) + 6) by ring.
          replace (4 * bt - 1 * (at_ + bt) - 18) with (2 * bt - 4 - (at_ - bt + 11) - 3) by ring.
          eapply Rconv; [exact R|ring|ring].
        * intros P n m1 m2 GP Gm2. rewrite Kk'. exact (pq_UD P n m1 m2 GP Gm2).
      + assert (Kk2 : phi kind = 2) by (pose proof (kind_cases (era b) (erb b)) as Kc'; change (kind_of (era b) (erb b)) with kind in Kc'; lia).
        assert (Kk' : kind = 2%uint63) by (apply to_Z_inj; exact Kk2).
        exists 1, 30, 14, 4, 116, 49, 581. split; [reflexivity|]. split; [unfold K2; rewrite Kk'; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros at_ bt Ra Rb (Gg1 & Gg2 & Gg3 & Gg4).
          destruct (res_kind (era b) (erb b) at_ bt Ra Rb) as [[K4 _]|[_ K5]]; [exfalso; change (kind_of (era b) (erb b)) with kind in K4; lia|].
          destruct (pairV at_ bt _ _ Ra Rb Gg1 Gg2 Gg3 Gg4 K5) as (_ & Pa & Pb). unfold ra1, rb1. rewrite Kk'. split; [|split; [exact Pa|exact Pb]].
          assert (Gd2 : (at_ - bt + 19) + 3 < 2 * bt - 8) by lia.
          pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ (XV _ _ Gg1 K5 Gg2 Gg3) (XD _ _ Gd2)) as R.
          unfold st_a, st_b. replace (at_ + bt + 14 - (4 * bt - 1 * (at_ + bt) - 30)) with (2 * (at_ - bt + 19) + 6) by ring.
          replace (4 * bt - 1 * (at_ + bt) - 30) with (2 * bt - 8 - (at_ - bt + 19) - 3) by ring.
          eapply Rconv; [exact R|ring|ring].
        * intros P n m1 m2 GP Gm2. rewrite Kk'. exact (pq_VD P n m1 m2 GP Gm2). }
  destruct Pr as (eZ & KZ & K2Z & ax & kx & kz & k0 & Ee1 & Ek2 & Bk & Bk2 & Eee & Pair & Pq).
  assert (Ee2' : eZ = 1 \/ eZ = 3) by exact Eee.
  assert (Eec : phi (ec b + K2)%uint63 = phi (ec b) + K2Z) by (rewrite <- Ek2; pv).
  (** lines are fine *)
  assert (LoOK : forall z, In z lo -> line_ok z).
  { intros z Hz. destruct (PL3 z Hz) as [Ha|(x & Hx & Hp)].
    - apply in_app_or in Ha. destruct Ha as [Ha|Ha]; [|eapply In_Forall; [exact BL|exact Ha]].
      destruct dl.
      + destruct Ha as [<-|[]]. unfold line_ok; cbn [lt lv]. rewrite El3v. split; [vm_compute; intro X0; discriminate X0|lia].
      + destruct Ha as [<-|[<-|[]]]; unfold line_ok; cbn [lt lv].
        * rewrite El1v. split; [vm_compute; intro X0; discriminate X0|lia].
        * split; [vm_compute; intro X0; discriminate X0|vm_compute; reflexivity].
    - exact (proj1 (pull_line_spec true e_ Wq (eW ch) yfx x z (In_Forall _ _ _ CL Hx) Ee' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp)). }
  assert (HiOK : forall z, In z hi -> line_ok z).
  { intros z Hz. destruct (PU3 z Hz) as [Ha|(x & Hx & Hp)].
    - apply in_app_or in Ha. destruct Ha as [Ha|Ha]; [|eapply In_Forall; [exact BU|exact Ha]].
      destruct dl.
      + destruct Ha.
      + destruct Ha as [<-|[]]. unfold line_ok; cbn [lt lv]. rewrite El2v. split; [vm_compute; intro X0; discriminate X0|lia].
    - exact (proj1 (pull_line_spec false e_ Wq (eW ch) yfx x z (In_Forall _ _ _ CU Hx) Ee' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp)). }
  (** the cost side *)
  destruct Hcb as (Obn & Obm1 & Obm2 & Obap & Obnd & Obmd1 & Obmd2 & Obp).
  destruct Hcc as (Ocn & Ocm1 & Ocm2 & Ocap & Ocnd & Ocmd1 & Ocmd2 & Ocp).
  pose proof (Pq (ep cc) (en cc) (em1 cc) (em2 cc) Ocp Ocm2) as PQ. cbv zeta in PQ. destruct PQ as [Gq1 Vq1].
  lazymatch type of HX with (if pok ?q then _ else _) = _ => destruct (pok q) eqn:Pq1 end; [|discriminate HX].
  pose proof (pok_good _ _ Gq1 Pq1) as Gq1'.
  lazymatch type of HX with (match ?o with Some _ => _ | None => _ end) = _ => destruct o as [s1|] eqn:Sh end; [|discriminate HX].
  destruct (shift_or (eY b) _ _ Gq1' ltac:(lia) Sh) as [Gs1 Vs1].
  lazymatch type of HX with (if ?c then _ else _) = _ => destruct c eqn:Cs end; [|discriminate HX].
  injection HX as <-. injection H as <-.
  apply andb_prop in Cs. destruct Cs as [Cs Kmd1].
  apply andb_prop in Cs. destruct Cs as [Cs Knd].
  apply andb_prop in Cs. destruct Cs as [Cs Kap].
  apply andb_prop in Cs. destruct Cs as [Cs Km1].
  apply andb_prop in Cs. destruct Cs as [Cs Kn].
  apply andb_prop in Cs. destruct Cs as [Cs Knmd2].
  apply andb_prop in Cs. destruct Cs as [Cs Knm2].
  apply andb_prop in Cs. destruct Cs as [Cs Kmd2].
  apply andb_prop in Cs. destruct Cs as [Cs Km2].
  apply andb_prop in Cs. destruct Cs as [Cs Kp].
  rename Cs into Ks1.
  apply ltb_true in Kmd1, Knd, Kap, Km1, Kn.
  change (phi 1152921504606846976%uint63) with 1152921504606846976 in Kmd1, Kap, Km1. change (phi 1073741824%uint63) with 1073741824 in Knd, Kn.
  pose proof (pok_good _ _ Gs1 Ks1) as Gs1'.
  set (y_ := phi (eY b)) in *.
  assert (Yb : 0 <= y_ < 1073741824) by (unfold y_; clear - BY BY0; lia).
  pose proof (phi_bd63 (en cc)) as Bnc. pose proof (phi_bd63 (em1 cc)) as Bm1c. pose proof (phi_bd63 (end_ cc)) as Bndc. pose proof (phi_bd63 (emd1 cc)) as Bmd1c.
  pose proof (phi_bd63 (en cb)) as Bnb. pose proof (phi_bd63 (em1 cb)) as Bm1b. pose proof (phi_bd63 (end_ cb)) as Bndb. pose proof (phi_bd63 (emd1 cb)) as Bmd1b.
  pose proof (phi_bd63 (eapps cb)) as Bapb. pose proof (phi_bd63 (eapps cc)) as Bapc.
  assert (NY : 0 <= phi (en cc) * y_ <= 1073741824 * 1073741824) by (split; [apply Z.mul_nonneg_nonneg|apply Z.mul_le_mono_nonneg]; clear - Ocn Bnc Yb; lia).
  assert (DY : 0 <= phi (end_ cc) * y_ <= 1073741824 * 1073741824) by (split; [apply Z.mul_nonneg_nonneg|apply Z.mul_le_mono_nonneg]; clear - Ocnd Bndc Yb; lia).
  assert (Em1c : phi (em1 cc + en cc * eY b)%uint63 = phi (em1 cc) + phi (en cc) * y_) by (apply phi_of_cg; [cgs|clear - Ocm1 NY Bm1c; lia]).
  assert (Emd1c : phi (emd1 cc + end_ cc * eY b)%uint63 = phi (emd1 cc) + phi (end_ cc) * y_) by (apply phi_of_cg; [cgs|clear - Ocmd1 DY Bmd1c; lia]).
  assert (Ep2 : phi (2 * em1 cc + en cc * eY b)%uint63 = 2 * phi (em1 cc) + phi (en cc) * y_) by (apply phi_of_cg; [cgs|clear - Ocm1 NY Bm1c; lia]).
  assert (Epd2 : phi (2 * emd1 cc + end_ cc * eY b)%uint63 = 2 * phi (emd1 cc) + phi (end_ cc) * y_) by (apply phi_of_cg; [cgs|clear - Ocmd1 DY Bmd1c; lia]).
  assert (Enn : phi (en cb + en cc)%uint63 = phi (en cb) + phi (en cc)) by (apply phi_of_cg; [cgs|clear - Obn Ocn Bnb Bnc; lia]).
  assert (Enm1 : phi (em1 cb + (em1 cc + en cc * eY b))%uint63 = phi (em1 cb) + (phi (em1 cc) + phi (en cc) * y_)).
  { apply phi_of_cg; [apply cg_add; [apply cg_refl|unfold cg; rewrite Em1c; reflexivity]|clear - Obm1 Ocm1 NY Bm1b Bm1c; lia]. }
  assert (Enap : phi (eapps cb + eapps cc + 2 * en cc)%uint63 = phi (eapps cb) + phi (eapps cc) + 2 * phi (en cc)) by (apply phi_of_cg; [cgs|clear - Obap Ocap Ocn Bapb Bapc Bnc; lia]).
  assert (Ennd : phi (end_ cb + end_ cc)%uint63 = phi (end_ cb) + phi (end_ cc)) by (apply phi_of_cg; [cgs|clear - Obnd Ocnd Bndb Bndc; lia]).
  assert (Enmd1 : phi (emd1 cb + (emd1 cc + end_ cc * eY b))%uint63 = phi (emd1 cb) + (phi (emd1 cc) + phi (end_ cc) * y_)).
  { apply phi_of_cg; [apply cg_add; [apply cg_refl|unfold cg; rewrite Emd1c; reflexivity]|clear - Obmd1 Ocmd1 DY Bmd1b Bmd1c; lia]. }
  destruct (pnat_spec (2 * em1 cc + en cc * eY b)%uint63) as [Gp2 Vp2].
  destruct (addk_spec (em2 cc) (eY b) _ _ _ Ocm2 Gp2 ltac:(fold y_; clear - Yb; lia) ltac:(clear; lia) ltac:(fold y_; clear - Yb; lia)) as [Gm2 Vm2].
  fold y_ in Vm2. rewrite Vp2, Ep2 in Vm2. pose proof (ok5_good _ _ Gm2 Km2) as Gm2'.
  destruct (pnat_spec (2 * emd1 cc + end_ cc * eY b)%uint63) as [Gpd2 Vpd2].
  destruct (addk_spec (emd2 cc) (eY b) _ _ _ Ocmd2 Gpd2 ltac:(fold y_; clear - Yb; lia) ltac:(clear; lia) ltac:(fold y_; clear - Yb; lia)) as [Gmd2 Vmd2].
  fold y_ in Vmd2. rewrite Vpd2, Epd2 in Vmd2. pose proof (ok5_good _ _ Gmd2 Kmd2) as Gmd2'.
  destruct (add5_spec (em2 cb) _ _ _ Obm2 Gm2' ltac:(clear; lia)) as [Gnm2 Vnm2]. pose proof (ok5_good _ _ Gnm2 Knm2) as Gnm2'.
  destruct (add5_spec (emd2 cb) _ _ _ Obmd2 Gmd2' ltac:(clear; lia)) as [Gnmd2 Vnmd2]. pose proof (ok5_good _ _ Gnmd2 Knmd2) as Gnmd2'.
  assert (Vp : forall b1 S1 g1, pval (padd (ep cb) s1) b1 S1 g1 = pval (ep cb) b1 S1 g1 + pval s1 b1 S1 g1).
  { intros b1 S1 g1. exact (proj2 (padd_spec (ep cb) s1 b1 S1 g1 _ _ Obp Gs1' ltac:(clear; lia))). }
  pose proof (padd_spec (ep cb) s1 0 0 0 _ _ Obp Gs1' ltac:(clear; lia)) as [Gp _]. pose proof (pok_good _ _ Gp Kp) as Gp'.
  assert (Cbd : cost_bd (mkC (en cb + en cc)%uint63 (em1 cb + (em1 cc + en cc * eY b))%uint63 (add5 (em2 cb) (addk (em2 cc) (eY b) (pnat (2 * em1 cc + en cc * eY b)%uint63)))
      (eapps cb + eapps cc + 2 * en cc)%uint63 (end_ cb + end_ cc)%uint63 (emd1 cb + (emd1 cc + end_ cc * eY b))%uint63
      (add5 (emd2 cb) (addk (emd2 cc) (eY b) (pnat (2 * emd1 cc + end_ cc * eY b)%uint63))) (padd (ep cb) s1))).
  { unfold cost_bd. cbn [en em1 em2 eapps end_ emd1 emd2 ep].
    exact (conj Kn (conj Km1 (conj Gnm2' (conj Kap (conj Knd (conj Kmd1 (conj Gnmd2' Gp'))))))). }
  split; [|exact Facts]. split; [exact Oks|]. split; [exact Cbd|].
  clear Facts Oks Sh.
  clear Obn Obm1 Obm2 Obap Obnd Obmd1 Obmd2 Obp Ocn Ocm1 Ocm2 Ocap Ocnd Ocmd1 Ocmd2 Ocp Gq1 Gq1' Pq1 Gs1 Gs1' Ks1 Kmd1 Knd Kap Km1 Kn Knmd2 Knm2 Kmd2 Km2 Kp
    Bnc Bm1c Bndc Bmd1c Bnb Bm1b Bndb Bmd1b Bapb Bapc NY DY Em1c Emd1c Ep2 Epd2 Gp2 Vp2 Gm2 Gm2' Gpd2 Vpd2 Gmd2 Gmd2' Gnm2 Gnm2' Gnmd2 Gnmd2' Gp Gp' Cbd Pq.
  assert (CE : hide ((phi (en cb + en cc)%uint63 = phi (en cb) + phi (en cc)) /\ (phi (em1 cb + (em1 cc + en cc * eY b))%uint63 = phi (em1 cb) + (phi (em1 cc) + phi (en cc) * y_)) /\
     (phi (eapps cb + eapps cc + 2 * en cc)%uint63 = phi (eapps cb) + phi (eapps cc) + 2 * phi (en cc)) /\ (phi (end_ cb + end_ cc)%uint63 = phi (end_ cb) + phi (end_ cc)) /\
     (phi (emd1 cb + (emd1 cc + end_ cc * eY b))%uint63 = phi (emd1 cb) + (phi (emd1 cc) + phi (end_ cc) * y_)) /\
     val5 (add5 (em2 cb) (addk (em2 cc) (eY b) (pnat (2 * em1 cc + en cc * eY b)%uint63))) = val5 (em2 cb) + val5 (addk (em2 cc) (eY b) (pnat (2 * em1 cc + en cc * eY b)%uint63)) /\
     val5 (add5 (emd2 cb) (addk (emd2 cc) (eY b) (pnat (2 * emd1 cc + end_ cc * eY b)%uint63))) = val5 (emd2 cb) + val5 (addk (emd2 cc) (eY b) (pnat (2 * emd1 cc + end_ cc * eY b)%uint63)) /\
     val5 (addk (em2 cc) (eY b) (pnat (2 * em1 cc + en cc * eY b)%uint63)) = val5 (em2 cc) + y_ * (2 * phi (em1 cc) + phi (en cc) * y_) /\
     val5 (addk (emd2 cc) (eY b) (pnat (2 * emd1 cc + end_ cc * eY b)%uint63)) = val5 (emd2 cc) + y_ * (2 * phi (emd1 cc) + phi (end_ cc) * y_))).
  { exact (conj Enn (conj Enm1 (conj Enap (conj Ennd (conj Enmd1 (conj Vnm2 (conj Vnmd2 (conj Vm2 Vmd2)))))))). }
  clear Enn Enm1 Enap Ennd Enmd1 Vnm2 Vnmd2 Vm2 Vmd2.
    intros B a b0 g len p0 p1 p2 len2 d0 d1 dc HS Ha Hb Hg HG Hreg HPre HDet. cbn [xs xk ec era erb ez ed2 eW eW1 eW2 elo ehi eY elast edet edlast edres eGm] in HS, Ha, Hb, HG, Hreg, HPre, HDet |- *.
    rewrite ElY in HPre. rewrite EY'. rewrite EGm in HG.
    unfold reg in Hreg. cbn [eW eW1 eW2 elo ehi] in Hreg.
    destruct Hreg as (RL & RU & R1 & R2). rewrite Forall_forall in RL, RU.
    rewrite phi_max, EW14 in R1. rewrite phi_min, EW24 in R2.
    assert (R1a : phi (eW1 b) * g <= PP * (a + b0)).
    { eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R1b : (4 * phi (eW1 ch)) * g <= PP * (a + b0)).
    { eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R2a : PP * (a + b0) <= phi (eW2 b) * g).
    { eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R2b : PP * (a + b0) <= (4 * phi (eW2 ch) - 64) * g).
    { eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia. }
    clear R1 R2.
    set (S := a + b0) in *. set (y := y_) in *.
    assert (Gg : phi (eGm b) <= g /\ phi gneed <= g /\ phi (eGm ch >> 2)%uint63 + 2 <= g) by (clear - HG; lia).
    clear HG. destruct Gg as (Gg1 & Gg2 & Gg3). rewrite Egn in Gg2.
    assert (HR : Reach (phi (ez b)) B (phi (ez b)) (B + y) (totn cb len len2) (totr cb p0 p1 p2 d0 d1 dc b0 S g)).
    { pose proof (XSb B a b0 g len p0 p1 p2 len2 d0 d1 dc) as XR. cbn [xs xk] in XR. refine (XR HS Ha Hb Hg Gg1 _ _ _).
      - unfold reg. repeat split; try assumption.
        + apply Forall_forall. intros x Hx. apply RL. apply PL1. apply in_or_app. right. exact Hx.
        + apply Forall_forall. intros x Hx. apply RU. apply PU1. apply in_or_app. right. exact Hx.
      - eapply XPre_mono; [|exact HPre]. clear - CL0 BL2. lia.
      - intros E1. rewrite E1 in HDet. cbn [orb] in HDet. specialize (HDet eq_refl).
        destruct (edet ch) eqn:Ed.
        + rewrite E1 in G16. cbn [negb orb] in G16. apply Uint63.eqb_spec in G16. rewrite G16.
          intros t Ht Hm. apply HDet; [rewrite phi_max; clear - Ht; lia|exact Hm].
        + intros t Ht Hm. apply HDet; [clear - Ht; lia|exact Hm]. }
    (** facts from the lines of the pair *)
    assert (Sg0 : 0 <= S).
    { pose proof (phi_bd63 (eW1 b)). assert (0 <= phi (eW1 b) * g) by (apply Z.mul_nonneg_nonneg; lia). lia. }
    assert (GgP : PP * (y + 64) <= g).
    { pose proof (phi_bd63 vm). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia. }
    assert (LL : if dl then 32 * g <= PP * (4 * (b0 + g * y) - 3 * S)
                 else 32 * g <= PP * (4 * (b0 + g * y) - 1 * S) /\ 16 * g <= PP * b0).
    { destruct dl.
      - assert (Rl : lo_l (phi (eW b)) (mkLine (3 * Q1)%uint63 (l3 + VOFF - yfx + 8)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. left. reflexivity. }
        unfold lo_l in Rl. cbn [lt lv] in Rl. rewrite El3v in Rl. change (phi (3 * Q1)%uint63) with (3 * 268435456) in Rl.
        apply (line_lo1 3 (phi (eW b)) y b0 S g (phi l3)); [|lia|lia].
        replace (phi l3 - y * PP + 8) with (phi l3 + VO - y * PP + 8 - VO) by ring. exact Rl.
      - assert (Rl : lo_l (phi (eW b)) (mkLine Q1 (l1 + VOFF - yfx + 8)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. left. reflexivity. }
        assert (Rl0 : lo_l (phi (eW b)) (mkLine 0%uint63 (VOFF + 16)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. right. left. reflexivity. }
        unfold lo_l in Rl, Rl0. cbn [lt lv] in Rl, Rl0. rewrite El1v in Rl. change (phi Q1) with (1 * 268435456) in Rl.
        change (phi 0%uint63) with 0 in Rl0. change (phi (VOFF + 16)%uint63 - VO) with 16 in Rl0. unfold lo_z in Rl0.
        split; [|lia].
        apply (line_lo1 1 (phi (eW b)) y b0 S g (phi l1)); [|lia|lia].
        replace (phi l1 - y * PP + 8) with (phi l1 + VO - y * PP + 8 - VO) by ring. exact Rl. }
    assert (HH : dl = false -> 32 * g <= PP * (2 * S - 4 * (b0 + g * (y + phi (elast ch))))).
    { intros Df. rewrite Df in *.
      assert (Rl : hi_l (phi (eW b)) (mkLine (2 * Q1)%uint63 (l2 + VOFF - ((eY b + elast ch) << 28) - 8)%uint63) b0 S g).
      { apply RU. apply PU1. apply in_or_app. left. left. reflexivity. }
      unfold hi_l in Rl. cbn [lt lv] in Rl. rewrite El2v in Rl. change (phi (2 * Q1)%uint63) with (2 * 268435456) in Rl.
      apply (line_hi1 2 (phi (eW b)) (y + phi (elast ch)) b0 S g (phi l2)); [|lia|lia].
      replace (phi l2 - (y + phi (elast ch)) * PP - 8) with (phi l2 + VO - (y + phi (elast ch)) * PP - 8 - VO) by ring. exact Rl. }
    (** the state at any visited offset *)
    assert (Gd : forall t, y <= t <= y + phi (elast ch) ->
       if dl then (a - (g - 1) * t) + 3 < b0 + g * t /\ (2 * (a - (g - 1) * t) + 6) + 3 < (b0 + g * t) - (a - (g - 1) * t) - 3
       else 5 <= b0 + g * t /\ b0 + g * t + 1 <= a - (g - 1) * t /\ 4 * (b0 + g * t) > (a - (g - 1) * t) + (b0 + g * t) + 30).
    { intros t Ht. destruct dl.
      - apply (guards_pairDD a b0 g S y t eq_refl Hg GgP ltac:(lia) ltac:(lia) ltac:(exact LL) Sg0).
      - destruct LL as [L1 L2]. apply (guards_pairUV a b0 g S y t (y + phi (elast ch)) eq_refl Hg GgP L2 ltac:(lia) ltac:(lia) (HH eq_refl) ltac:(lia)). }
    assert (Ka : forall t, t mod 4 = 0 -> phi (era b) = (a - (g - 1) * t) mod 4) by (intros t Ht; rewrite res_at by exact Ht; symmetry; exact Ha).
    assert (Kb : forall t, t mod 4 = 0 -> phi (erb b) = (b0 + g * t) mod 4) by (intros t Ht; rewrite resb_at by exact Ht; symmetry; exact Hb).
    assert (Odd : dl = false -> forall t, t mod 4 = 0 -> (b0 + g * t) mod 2 = 1).
    { intros Df t Ht. rewrite Df in G6. cbn [orb] in G6. apply eqb_true in G6. rewrite phi_land1 in G6. change (phi 1%uint63) with 1 in G6.
      pose proof (Kb t Ht) as Kbt. rewrite Kbt in G6. revert G6. clear -Ht. intros G6. Z.div_mod_to_equations. lia. }
    assert (W : forall t, y <= t <= y + phi (elast ch) -> t mod 4 = 0 ->
        Reach (a - (g - 1) * t) (b0 + g * t) (st_a eZ KZ K2Z (a - (g - 1) * t) (b0 + g * t)) (st_b eZ KZ (a - (g - 1) * t) (b0 + g * t)) 2
          (ax * ((b0 + g * t) * ((a - (g - 1) * t) + (b0 + g * t))) + kx * (b0 + g * t) - kz * ((a - (g - 1) * t) + (b0 + g * t)) - k0) /\
        phi (ra_next ra1 rb1 0) = st_a eZ KZ K2Z (a - (g - 1) * t) (b0 + g * t) mod 4 /\ phi (rb_next ra1 rb1 0) = st_b eZ KZ (a - (g - 1) * t) (b0 + g * t) mod 4).
    { intros t Ht Hm. apply Pair; [apply Ka; exact Hm|apply Kb; exact Hm|].
      pose proof (Gd t Ht) as Gt. destruct dl; [exact Gt|]. destruct Gt as (G1a & G1b & G1c). repeat split; try assumption. apply Odd; [reflexivity|exact Hm]. }
    clear Ha Hb.
    set (at0 := a - (g - 1) * y). set (bt0 := b0 + g * y).
    set (a2 := st_a eZ KZ K2Z at0 bt0). set (b2 := st_b eZ KZ at0 bt0). set (g2 := 4 * g - eZ).
    assert (Sum0 : at0 + bt0 = S + y) by (unfold at0, bt0, S; ring).
    assert (Eb2 : b2 = 4 * (b0 + g * y) - eZ * (S + y) - KZ) by (unfold b2, st_b; rewrite Sum0; unfold bt0; ring).
    assert (Es2 : a2 + b2 = S + y + K2Z) by (unfold a2, st_a; fold b2; lia).
    assert (Y4 : y mod 4 = 0).
    { rewrite Ky. replace (4 * ky) with (0 + ky * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
    destruct (W y ltac:(lia) Y4) as (W1_ & W2_ & W3_). fold at0 bt0 a2 b2 in W1_, W2_, W3_.
    assert (HC : Reach (phi (ez ch)) (B + y) (phi (ez ch)) (B + y + phi (eY ch)) (totn cc (len + 2) len2)
        (totr cc (p0 + p1 * y + p2 * (y * y) + (ax * (bt0 * (S + y)) + kx * bt0 - kz * (S + y) - k0)) (p1 + 2 * p2 * y + ax * (bt0 + g * (S + y)) + kx * g - kz) (p2 + ax * g)
          (d0 + d1 * y + dc * (y * y)) (d1 + 2 * dc * y) dc b2 (a2 + b2) g2)).
    { apply (XSc (B + y) a2 b2 g2 (len + 2) _ _ _ len2 _ _ _); cbn [xs xk].
      - rewrite Es2. rewrite G1. rewrite Eec. clear - HS. lia.
      - rewrite G2. symmetry. exact W2_.
      - rewrite G3. symmetry. exact W3_.
      - unfold g2. clear - Hg Eee. lia.
      - unfold g2. clear - Hg Eee Gg3 GcD. lia.
      - (* region *)
        rewrite Es2, Eb2. unfold reg. repeat split.
        + apply Forall_forall. intros x Hx.
          destruct (PL2 x Hx) as (z & Hp & Hz).
          eapply (lo_pulled e_ Wq (eW ch) yfx x z (phi (eW b)) y eZ KZ K2Z b0 S g (phi (eW2 b))); try lia.
          * eapply In_Forall; [exact CL|exact Hx].
          * pose proof (Mv4 x Hx). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia.
          * exact Hp.
          * apply RL. exact Hz.
        + apply Forall_forall. intros x Hx.
          destruct (PU2 x Hx) as (z & Hp & Hz).
          eapply (hi_pulled e_ Wq (eW ch) yfx x z (phi (eW b)) y eZ KZ K2Z b0 S g (phi (eW1 b))); try lia.
          * eapply In_Forall; [exact CU|exact Hx].
          * pose proof (Mv2 x Hx). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia.
          * exact Hp.
          * apply RU. exact Hz.
        + unfold g2. apply (range_lo _ (4 * phi (eW1 ch))); try lia. pose proof (phi_bd63 (eW1 ch)). lia.
        + unfold g2. pose proof (phi_bd63 (eW2 ch)). pose proof (phi_bd63 vm). pose proof (phi_bd63 (eW ch)). apply (range_hi _ (4 * phi (eW2 ch) - 64)); lia.
      - (* the prefix *)
        rewrite G4. intros y' Hy' Hm.
        assert (Ht4 : (y + y') mod 4 = 0).
        { rewrite Z.add_mod by lia. rewrite Y4, Hm. reflexivity. }
        pose proof (HPre (y + y') ltac:(lia) Ht4) as P1.
        destruct (W (y + y') ltac:(lia) Ht4) as (P2 & _ & _).
        replace (B + y + y') with (B + (y + y')) by ring.
        replace (a2 - (g2 - 1) * y') with (st_a eZ KZ K2Z (a - (g - 1) * (y + y')) (b0 + g * (y + y'))) by (unfold a2, st_a, b2, st_b, g2, at0, bt0; ring).
        replace (b2 + g2 * y') with (st_b eZ KZ (a - (g - 1) * (y + y')) (b0 + g * (y + y'))) by (unfold b2, st_b, g2, at0, bt0; ring).
        eapply Rconv; [exact (Reach_trans _ _ _ _ _ _ _ _ _ _ P1 P2)|ring|unfold bt0, S; ring].
      - (* the detour *)
        intros E1. rewrite E1 in HDet. rewrite orb_true_r in HDet. specialize (HDet eq_refl). rewrite G4, G5.
        cbv iota in HDet. rewrite phi_max in HDet.
        intros y' Hy' Hm.
        replace (B + y + y') with (B + (y + y')) by ring.
        eapply Rconv; [apply HDet; [lia|]|reflexivity|ring]. rewrite Z.add_mod by lia. rewrite Y4. rewrite Z.add_0_l, Z.mod_mod by lia. exact Hm. }
    rewrite G4 in HC. pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ HR HC) as RT.
    replace (B + (y + phi (eY ch))) with (B + y + phi (eY ch)) by ring.
    eapply Rconv; [exact RT| |].
    + unfold hide in CE. destruct CE as (Enn & Enm1 & Enap & Ennd & Enmd1 & Vnm2 & Vnmd2 & Vm2 & Vmd2).
      unfold totn. cbn [en eapps end_]. rewrite Enn, Enap, Ennd. atomize. ring.
    + unfold hide in CE. destruct CE as (Enn & Enm1 & Enap & Ennd & Enmd1 & Vnm2 & Vnmd2 & Vm2 & Vmd2).
      unfold totr. cbn [en em1 em2 end_ emd1 emd2 ep]. rewrite Enn, Enm1, Ennd, Enmd1, Vnm2, Vnmd2, Vm2, Vmd2, Vp, Vs1, Vq1.
      rewrite Es2, Eb2. unfold g2. atomize. unfold bt0. clear - HS. revert HS. generalize S y. intros. ring.
Qed.
