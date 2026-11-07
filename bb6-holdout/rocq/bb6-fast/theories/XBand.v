(** The band recursion with exact counts: finishing keeps the cost, a table of [XEnt], the recursion over nodes. *)
From Coq Require Import ZArith Lia Uint63 List Bool PArray.
Import ListNotations.
From BB6 Require Import Map Walk Num.
From BF Require Import Ints HLines HCore HAbs HBand XCost XCore XAbs.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** What finishing keeps: everything but the region, which only shrinks. *)
Definition same_out (b e : Ent) : Prop :=
  ent_bd e /\ ec e = ec b /\ era e = era b /\ erb e = erb b /\ ez e = ez b /\ ed2 e = ed2 b /\ eY e = eY b /\ elast e = elast b /\
  edet e = edet b /\ edlast e = edlast b /\ edres e = edres b /\ eGm e = eGm b /\
  forall b0 S0 g, 1 <= g -> reg e b0 S0 g -> reg b b0 S0 g.

Lemma finish_try_reg f b W W1 W2 e :
  ent_ok b -> phi W <= 1152921504606846976 -> phi (eW1 b) <= phi W1 -> phi W2 <= phi (eW2 b) -> phi W1 <= phi W <= phi W2 ->
  phi W - 1073741824 <= phi W1 -> phi W2 <= phi W + 1073741824 -> W = eW b ->
  finish_try f b W W1 W2 = Some e -> same_out b e.
Proof.
  revert W1 W2. induction f as [|f IH]; intros W1 W2 Hb HW H1 H2 H3 H4 H5 HE H; [discriminate|].
  cbn [finish_try] in H. cbv zeta in H.
  destruct ((Nat.leb (List.length (lo_keep (eW b) W1 W2 (elo b) [])) KF) && (Nat.leb (List.length (hi_keep (eW b) W1 W2 (ehi b) [])) KF)) eqn:C.
  2:{ pose proof (phi_bd63 W1). pose proof (phi_bd63 W2). pose proof (phi_bd63 (eW2 b)). assert (Ma : phi (W - W1)%uint63 = phi W - phi W1) by pv.
      assert (Mb : phi (W2 - W)%uint63 = phi W2 - phi W) by pv.
      assert (Mc : phi ((W - W1) >> 1)%uint63 = (phi W - phi W1) / 2) by (rewrite lsr_spec, Ma; reflexivity).
      assert (Md : phi ((W2 - W) >> 1)%uint63 = (phi W2 - phi W) / 2) by (rewrite lsr_spec, Mb; reflexivity).
      assert (Bc : 0 <= (phi W - phi W1) / 2 <= phi W - phi W1) by (clear -H3; Z.div_mod_to_equations; lia).
      assert (Bd : 0 <= (phi W2 - phi W) / 2 <= phi W2 - phi W) by (clear -H3; Z.div_mod_to_equations; lia).
      assert (Me : phi (W - ((W - W1) >> 1))%uint63 = phi W - (phi W - phi W1) / 2) by (rewrite <- Mc; pv).
      assert (Mf : phi (W + ((W2 - W) >> 1))%uint63 = phi W + (phi W2 - phi W) / 2) by (rewrite <- Md; pv).
      apply (IH (W - ((W - W1) >> 1))%uint63 (W + ((W2 - W) >> 1))%uint63 Hb HW); try exact H; try exact HE; lia. }
  destruct (forallb line_okb (finL (lo_keep (eW b) W1 W2 (elo b) [])) && forallb line_okb (finL (hi_keep (eW b) W1 W2 (ehi b) []))
         && forallb (fun x => existsb (fun k => dom_lo_b (eW b) W1 W2 k x) (finL (lo_keep (eW b) W1 W2 (elo b) []))) (elo b)
         && forallb (fun x => existsb (fun k => dom_hi_b (eW b) W1 W2 k x) (finL (hi_keep (eW b) W1 W2 (ehi b) []))) (ehi b)) eqn:G; [|discriminate].
  injection H as <-.
  apply andb_prop in G. destruct G as [G G4]. apply andb_prop in G. destruct G as [G G3]. apply andb_prop in G. destruct G as [G1 G2].
  set (lo := finL (lo_keep (eW b) W1 W2 (elo b) [])) in *.
  set (hi := finL (hi_keep (eW b) W1 W2 (ehi b) [])) in *.
  clearbody lo hi.
  rewrite forallb_forall in G1, G2, G3, G4.
  destruct Hb as [Bd Sem]. destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  subst W.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]]]]]]]]].
  - unfold ent_bd; cbn [elo ehi eW eW1 eW2 eY elast edlast eGm ec]. repeat split; try lia; try assumption.
    + apply Forall_forall. intros x Hx. apply line_okb_spec. apply G1. exact Hx.
    + apply Forall_forall. intros x Hx. apply line_okb_spec. apply G2. exact Hx.
  - intros b0 S0 g Hg Hreg.
    unfold reg in Hreg. cbn [eW eW1 eW2 elo ehi] in Hreg. destruct Hreg as (RL & RU & R1 & R2). rewrite Forall_forall in RL, RU.
    assert (B0 : 0 <= phi (eW1 b)) by (pose proof (phi_bd63 (eW1 b)); lia).
    unfold reg. repeat split.
    + apply Forall_forall. intros x Hx. pose proof (G3 x Hx) as Ex. apply existsb_exists in Ex. destruct Ex as (k & Hk & Dk).
      apply (dom_lo_sound (eW b) W1 W2 k x b0 S0 g); try assumption; try lia.
      * apply line_okb_spec. apply G1. exact Hk.
      * eapply In_Forall; [exact BL|exact Hx].
      * apply RL. exact Hk.
    + apply Forall_forall. intros x Hx. pose proof (G4 x Hx) as Ex. apply existsb_exists in Ex. destruct Ex as (k & Hk & Dk).
      apply (dom_hi_sound (eW b) W1 W2 k x b0 S0 g); try assumption; try lia.
      * apply line_okb_spec. apply G2. exact Hk.
      * eapply In_Forall; [exact BU|exact Hx].
      * apply RU. exact Hk.
    + eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia.
    + eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma finish_reg b beta W e : ent_ok b -> finish b beta W = Some e -> same_out b e.
Proof.
  intros Hb H. unfold finish, finish_w in H. cbv zeta in H.
  set (W1 := max_ (eW1 b) (if (1073741824 <=? W)%uint63 then (W - 1073741824)%uint63 else 0%uint63)) in *.
  set (W2 := min_ (eW2 b) (W + 1073741824)%uint63) in *.
  destruct ((W1 <=? W)%uint63 && (W <=? W2)%uint63 && (W =? eW b)%uint63 && (W <=? 1152921504606846976)%uint63) eqn:C; [|discriminate].
  apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  apply leb_true in C1, C2, C4. apply Uint63.eqb_spec in C3. change (phi 1152921504606846976%uint63) with 1152921504606846976 in C4.
  destruct (finish_try 4 b W W1 W2) as [e'|] eqn:F; [|discriminate].
  assert (He' : same_out b e').
  { apply (finish_try_reg 4 b W W1 W2 e' Hb C4); try exact F; try exact C3; try lia.
    - unfold W1. rewrite phi_max. lia.
    - unfold W2. rewrite phi_min. lia.
    - unfold W1. rewrite phi_max. destruct (1073741824 <=? W)%uint63 eqn:D.
      + apply leb_true in D. change (phi 1073741824%uint63) with 1073741824 in D. assert (X : phi (W - 1073741824)%uint63 = phi W - 1073741824) by pv. lia.
      + apply leb_false in D. change (phi 1073741824%uint63) with 1073741824 in D. change (phi 0%uint63) with 0. lia.
    - unfold W2. rewrite phi_min. assert (X : phi (W + 1073741824)%uint63 = phi W + 1073741824) by pv. lia. }
  destruct (in_region e' beta W); [|discriminate]. injection H as <-. exact He'.
Qed.

Lemma same_out_X b e c : same_out b e -> X_sem (mkX b c) -> X_sem (mkX e c).
Proof.
  intros (_ & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & R) H B a b0 g len p0 p1 p2 len2 d0 d1 dc HS Ha Hb Hg HG Hreg HPre HDet.
  cbn [xs xk] in *. rewrite E1 in HS. rewrite E2 in Ha. rewrite E3 in Hb. rewrite E11 in HG. rewrite E4, E7 in HPre. rewrite E8, E4, E5, E9, E10 in HDet. rewrite E4, E6.
  exact (H B a b0 g len p0 p1 p2 len2 d0 d1 dc HS Ha Hb Hg HG (R _ _ _ Hg Hreg) HPre HDet).
Qed.

Definition x_finish (b : XEnt) (beta W : int) : option XEnt :=
  match finish (xs b) beta W with Some e => Some (mkX e (xk b)) | None => None end.
Lemma x_finish_sound b beta W e : x_ok b -> x_finish b beta W = Some e -> x_ok e.
Proof.
  destruct b as [b c]. intros (Hb & Hc & Hs) H. unfold x_finish in H. cbn [xs xk] in *.
  destruct (finish b beta W) as [e'|] eqn:F; [|discriminate H]. injection H as <-.
  pose proof (finish_reg b beta W e' Hb F) as So.
  split; [|split; [exact Hc|exact (same_out_X b e' c So Hs)]].
  pose proof (finish_sound b beta W e' Hb F) as Ok. exact Ok.
Qed.

(** The empty block, cost zero. *)
Definition cost0 : Cost := mkC 0 0 zero5 0 0 0 zero5 poly0.
Definition xbld0 (v : Env) (x : Ctx) (W : int) : XEnt := mkX (bld0 v x W) cost0.
Lemma pval0 b S g : pval poly0 b S g = 0.
Proof. unfold pval, poly0. cbn [pA pB pC pD pE pF pG pH pI pJ]. change (val5 zero5) with 0. ring. Qed.
Lemma xbld0_ok v x W : phi (xc x) < 1099511627776 -> phi W <= 1152921504606846976 -> x_ok (xbld0 v x W).
Proof.
  intros Hc HW. split; [exact (bld0_ok v x W Hc HW)|]. split.
  - unfold cost_bd, cost0. cbn [en em1 em2 eapps end_ emd1 emd2 ep].
    destruct zero5_spec as [G0 _]. assert (G1 : good5 1073741824 zero5) by (eapply good_mono; [|exact G0]; lia).
    refine (conj _ (conj _ (conj G1 (conj _ (conj _ (conj _ (conj G1 _))))))); try (vm_compute; reflexivity).
    unfold pgood, poly0; cbn [pA pB pC pD pE pF pG pH pI pJ]. exact (conj G1 (conj G1 (conj G1 (conj G1 (conj G1 (conj G1 (conj G1 (conj G1 (conj G1 G1))))))))).
  - intros B a b0 g len p0 p1 p2 len2 d0 d1 dc _ _ _ _ _ _ _ _. unfold xbld0, bld0. cbn [xs xk eY ez]. change (phi 0%uint63) with 0. rewrite Z.add_0_r.
    unfold totn, totr, cost0. cbn [en em1 em2 eapps end_ emd1 emd2 ep]. rewrite pval0. change (phi 0%uint63) with 0. change (val5 zero5) with 0.
    eapply Rconv; [apply Reach_refl|ring|ring].
Qed.

(** ** The table *)
Inductive XTr := XL | XN (kc klo khi : int) (e : XEnt) (l r : XTr).
Record XMem := mkXMem { xmt : array XTr; xmn : int }.
Definition XLIMIT : int := 500000.
Definition xmem0 (_ : int) : XMem := mkXMem (PArray.make TSIZE XL) 0.

Fixpoint xlook (t : XTr) (v : Env) (x : Ctx) (beta W : int) : option XEnt :=
  match t with
  | XL => None
  | XN k klo khi e l r =>
    if (beta <? klo)%uint63 then xlook l v x beta W
    else if (khi <? beta)%uint63 then xlook r v x beta W
    else if keyok v x (xs e) && in_region (xs e) beta W then Some e
    else if (beta <? k)%uint63 then xlook l v x beta W else xlook r v x beta W
  end.
Fixpoint xins (t : XTr) (k klo khi : int) (e : XEnt) : XTr :=
  match t with
  | XL => XN k klo khi e XL XL
  | XN k' a b e' l r => if (k <? k')%uint63 then XN k' a b e' (xins l k klo khi e) r else XN k' a b e' l (xins r k klo khi e)
  end.

Fixpoint xtr_ok (t : XTr) : Prop :=
  match t with XL => True | XN _ _ _ e l r => x_ok e /\ xtr_ok l /\ xtr_ok r end.
Lemma xlook_sound t v x beta W e : xtr_ok t -> xlook t v x beta W = Some e -> x_ok e.
Proof.
  induction t as [|k klo khi e' l IHl r IHr]; intros Ht H; cbn in H; [discriminate|].
  destruct Ht as (He & Hl & Hr).
  destruct (beta <? klo)%uint63; [apply IHl; assumption|].
  destruct (khi <? beta)%uint63; [apply IHr; assumption|].
  destruct (keyok v x (xs e') && in_region (xs e') beta W); [injection H as <-; exact He|].
  destruct (beta <? k)%uint63; [apply IHl; assumption|apply IHr; assumption].
Qed.
Lemma xins_ok t k klo khi e : xtr_ok t -> x_ok e -> xtr_ok (xins t k klo khi e).
Proof.
  induction t as [|k' a b e' l IHl r IHr]; intros Ht He; cbn.
  - exact (conj He (conj I I)).
  - destruct Ht as (H1 & H2 & H3). destruct (k <? k')%uint63; cbn.
    + exact (conj H1 (conj (IHl H2 He) H3)).
    + exact (conj H1 (conj H2 (IHr H3 He))).
Qed.
Definition xmem_ok (m : XMem) : Prop := forall i, xtr_ok (PArray.get (xmt m) i).
Lemma xmem0_ok u : xmem_ok (xmem0 u).
Proof. intros i. unfold xmem0. cbn [xmt]. rewrite PArray.get_make. exact I. Qed.
Lemma xmem_set_ok t s k klo khi e : (forall i, xtr_ok (PArray.get t i)) -> x_ok e ->
  forall i, xtr_ok (PArray.get (PArray.set t s (xins (PArray.get t s) k klo khi e)) i).
Proof.
  intros Ht He i. destruct (s =? i)%uint63 eqn:Es.
  - apply Uint63.eqb_spec in Es. subst i. destruct (s <? PArray.length t)%uint63 eqn:L.
    + rewrite PArray.get_set_same by exact L. apply xins_ok; [apply Ht|exact He].
    + assert (Hd : PArray.get (PArray.set t s (xins (PArray.get t s) k klo khi e)) s = PArray.get t s).
      { rewrite PArray.get_out_of_bounds by (rewrite PArray.length_set; exact L).
        rewrite PArray.default_set. rewrite PArray.get_out_of_bounds by exact L. reflexivity. }
      rewrite Hd. apply Ht.
  - apply Uint63.eqb_false_spec in Es. rewrite PArray.get_set_other by exact Es. apply Ht.
Qed.


(** ** The recursion *)
Fixpoint xsec_go (rec : XMem -> Ctx -> int -> int -> XMem * option XEnt) (v : Env) (x11 x00 : Ctx) (beta W w4 w2 w34 : int)
    (g : nat) (m : XMem) (b : XEnt) : XMem * option XEnt :=
  match g with
  | O => (m, None)
  | S g' =>
    let pos := (beta + (eY (xs b) << 28))%uint63 in
    if (W + 64 <=? pos)%uint63 then (m, Some b)
    else if (W <=? pos + 64)%uint63 then (m, None)
    else if (pos + 64 <? w4)%uint63 then
      match x_stop b v false beta with
      | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g' m b2
      | None => (m, None)
      end
    else if (pos <? w4 + 64)%uint63 then (m, None)
    else if (pos + 64 <? w2)%uint63 then
      let '(m1, och) := rec m x11 (pos - w4)%uint63 w4 in
      match och with
      | None => (m1, None)
      | Some ch =>
        match x_absorb b ch false with
        | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g' m1 b2
        | None => (m1, None)
        end
      end
    else if (pos <? w2 + 64)%uint63 then (m, None)
    else if (pos + 64 <? w34)%uint63 then
      match x_stop b v true beta with
      | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g' m b2
      | None => (m, None)
      end
    else if (pos <? w34 + 64)%uint63 then (m, None)
    else
      let '(m1, och) := rec m x00 (pos - w34)%uint63 w4 in
      match och with
      | None => (m1, None)
      | Some ch =>
        match x_absorb b ch true with
        | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g' m1 b2
        | None => (m1, None)
        end
      end
  end.

Definition xsec_loop (rec : XMem -> Ctx -> int -> int -> XMem * option XEnt) (v : Env) (x : Ctx) (beta W : int) (g : nat) (m : XMem) (b : XEnt) : XMem * option XEnt :=
  let ra := xra x in let rb := xrb x in let c := xc x in
  let w4 := (W >> 2)%uint63 in
  let kind := kind_of ra rb in
  let ra1 := ra_next ra rb kind in let rb1 := rb_next ra rb kind in
  let c1 := (c + kcost kind)%uint63 in
  let ra0 := ra_next ra rb 0 in let rb0 := rb_next ra rb 0 in
  xsec_go rec v (mkCtx (c1 + 3)%uint63 (ra_next ra1 rb1 0) (rb_next ra1 rb1 0)) (mkCtx (c + 6)%uint63 (ra_next ra0 rb0 0) (rb_next ra0 rb0 0))
    beta W w4 (W >> 1)%uint63 (3 * w4)%uint63 g m b.

Fixpoint xbn (f : nat) (m : XMem) (v : Env) (x : Ctx) (beta W : int) : XMem * option XEnt :=
  match f with
  | O => (m, None)
  | S f' =>
    if (beta <? 32)%uint63 || (W <? 8192)%uint63 || (1152921504606846976 <? W)%uint63 || (1099511627776 <=? xc x)%uint63 then (m, None) else
    let memo := (WMIN <=? W)%uint63 in
    let s := if memo then slot v x W else 0%uint63 in
    match (if memo then xlook (PArray.get (xmt m) s) v x beta W else None) with
    | Some e => (m, Some e)
    | None =>
      let '(m1, ob) := xsec_loop (fun m' x' b' W' => xbn f' m' v x' b' W') v x beta W Lfuel m (xbld0 v x W) in
      match ob with
      | None => (m1, None)
      | Some b =>
        match x_finish b beta W with
        | None => (m1, None)
        | Some e =>
          if memo then
            let dW := (W - eW1 (xs e))%uint63 in
            let klo := (maxlo (elo (xs e)) dW 0 - VOFF)%uint63 in
            let khi := (minhi (ehi (xs e)) dW 4611686018427387903 - VOFF)%uint63 in
            let m2 := if (XLIMIT <=? xmn m1)%uint63 then xmem0 0%uint63 else m1 in
            (mkXMem (PArray.set (xmt m2) s (xins (PArray.get (xmt m2) s) ((klo + khi) >> 1)%uint63 klo khi e)) (xmn m2 + 1)%uint63, Some e)
          else (m1, Some e)
        end
      end
    end
  end.


(** ** Soundness of the recursion *)
Definition xres_ok (r : XMem * option XEnt) : Prop := xmem_ok (fst r) /\ forall e, snd r = Some e -> x_ok e.

Lemma xsec_go_sound rec v x11 x00 beta W w4 w2 w34 : phi (vz v) = 6 \/ phi (vz v) = 22 ->
  (forall m x' b' W', xmem_ok m -> xres_ok (rec m x' b' W')) ->
  forall g m b, xmem_ok m -> x_ok b -> xres_ok (xsec_go rec v x11 x00 beta W w4 w2 w34 g m b).
Proof.
  intros Hz Hrec. induction g as [|g IH]; intros m b Hm Hb.
  { split; [exact Hm|intros e H; discriminate]. }
  cbn [xsec_go]. cbv zeta.
  assert (St : forall dl, xres_ok match x_stop b v dl beta with
      | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g m b2
      | None => (m, None) end).
  { intros dl. destruct (x_stop b v dl beta) as [b2|] eqn:S.
    - apply IH; [exact Hm|]. exact (proj1 (x_stop_sound b v dl beta b2 Hb Hz S)).
    - split; [exact Hm|intros e H; discriminate]. }
  assert (Ch : forall X Y Z dl, xres_ok (let '(m1, och) := rec m X Y Z in
      match och with
      | None => (m1, None)
      | Some ch =>
        match x_absorb b ch dl with
        | Some b2 => xsec_go rec v x11 x00 beta W w4 w2 w34 g m1 b2
        | None => (m1, None)
        end
      end)).
  { intros X Y Z dl. destruct (Hrec m X Y Z Hm) as [H1 H2]. destruct (rec m X Y Z) as [m1 och]. cbn [fst snd] in H1, H2.
    destruct och as [ch|].
    - destruct (x_absorb b ch dl) as [b2|] eqn:A.
      + apply IH; [exact H1|]. exact (proj1 (x_absorb_sound b ch dl b2 Hb (H2 ch eq_refl) A)).
      + split; [exact H1|intros e H; discriminate].
    - split; [exact H1|intros e H; discriminate]. }
  assert (N1 : xres_ok (m, None)) by (split; [exact Hm|intros e H; discriminate]).
  assert (N2 : xres_ok (m, Some b)) by (split; [exact Hm|intros e H; injection H as <-; exact Hb]).
  repeat (match goal with |- xres_ok (if ?c then _ else _) => destruct c end); try assumption; try apply St; try apply Ch.
Qed.

Theorem xbn_sound f : forall m v x beta W, phi (vz v) = 6 \/ phi (vz v) = 22 -> xmem_ok m -> xres_ok (xbn f m v x beta W).
Proof.
  induction f as [|f IH]; intros m v x beta W Hz Hm.
  { split; [exact Hm|intros e H; discriminate]. }
  cbn [xbn].
  destruct ((beta <? 32)%uint63 || (W <? 8192)%uint63 || (1152921504606846976 <? W)%uint63 || (1099511627776 <=? xc x)%uint63) eqn:C.
  { split; [exact Hm|intros e H; discriminate]. }
  repeat (apply orb_false_iff in C; destruct C as [C ?]). rename H into C4. rename H0 into C3. rename H1 into C2.
  apply ltb_false in C3. apply leb_false in C4. change (phi 1152921504606846976%uint63) with 1152921504606846976 in C3. change (phi 1099511627776%uint63) with 1099511627776 in C4.
  cbv zeta.
  set (s := if (WMIN <=? W)%uint63 then slot v x W else 0%uint63).
  destruct (if (WMIN <=? W)%uint63 then xlook (PArray.get (xmt m) s) v x beta W else None) as [e|] eqn:L.
  { split; [exact Hm|]. intros e' H. cbn in H. injection H as <-. destruct (WMIN <=? W)%uint63; [|discriminate]. eapply xlook_sound; [apply Hm|exact L]. }
  assert (HS : xres_ok (xsec_loop (fun m' x' b' W' => xbn f m' v x' b' W') v x beta W Lfuel m (xbld0 v x W))).
  { unfold xsec_loop. cbv zeta. apply xsec_go_sound; [exact Hz|intros m' x' b' W' Hm'; apply IH; assumption|exact Hm|apply xbld0_ok; assumption]. }
  destruct (xsec_loop (fun m' x' b' W' => xbn f m' v x' b' W') v x beta W Lfuel m (xbld0 v x W)) as [m1 ob].
  destruct HS as [H1 H2]. cbn [fst snd] in H1, H2.
  destruct ob as [b|]; [|split; [exact H1|intros e H; discriminate]].
  destruct (x_finish b beta W) as [e|] eqn:F; [|split; [exact H1|intros e H; discriminate]].
  assert (He : x_ok e) by exact (x_finish_sound b beta W e (H2 b eq_refl) F).
  destruct (WMIN <=? W)%uint63.
  - set (m2 := if (XLIMIT <=? xmn m1)%uint63 then xmem0 0%uint63 else m1).
    assert (Hm2 : xmem_ok m2) by (unfold m2; destruct (XLIMIT <=? xmn m1)%uint63; [apply xmem0_ok|exact H1]).
    split.
    + intros i. cbn [fst xmt]. apply xmem_set_ok; [exact Hm2|exact He].
    + intros e' H. cbn [snd] in H. injection H as <-. exact He.
  - split; [exact H1|]. intros e' H. cbn [snd] in H. injection H as <-. exact He.
Qed.
