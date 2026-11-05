(** Verifier for closed automaton certificates (new; not in Coq-BB5).

  A certificate describes a set of abstract configurations closed under the machine's step:
  - cell labels `x`, each standing for a real symbol (`ac_X`), and control labels `q`, each standing for a
    machine state (`ac_Q`); labels may carry extra information (e.g. history), which only the certificate uses;
  - edge sets `ac_EL`, `ac_ER` of triples (a,x,b): reading a cell labelled x moves an automaton from a to b.
    Each side of the tape is read from far away towards the head;
  - for each side a set of "blank" states (`ac_CL`, `ac_CR`) where reading starts: every such state must be
    entered from another such state by an edge labelled with a Σ0 cell, which covers the infinite blank part;
  - a set `ac_C` of abstract configurations (l,q,x,r).

  A configuration (left cells, state, head cell, right cells) is covered if some (l,q,x,r) in `ac_C` has
  q standing for the state, x for the head symbol, and paths over the left and right cells to l and r.
  The checker verifies that the start configuration is covered and that every abstract configuration has a
  defined transition whose result is covered again (for all ways the far side can be popped). By induction
  the machine then runs forever from the start configuration.

  This is the theorem of `least-verify/code/check/check_cert.py`, restricted to deterministic labels. *)

Require Import List.
Require Import Lia.
Require Import ZArith.
Require Import FSets.FMapPositive.

From BBminus2x4 Require Import Prelims.
From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import BB2x4_Encodings.
From BBminus2x4 Require Import Tactics.
From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import List_Tape.
From BBminus2x4 Require Import Deciders_Common.

Record AutCert := {
  ac_X: list (positive*Σ);
  ac_Q: list (positive*St);
  ac_EL: list (positive*positive*positive);
  ac_ER: list (positive*positive*positive);
  ac_CL: list positive;
  ac_CR: list positive;
  ac_C: list (positive*positive*positive*positive);
}.

(* Begin: lookup structures *)

Fixpoint map_of_list{T}(ls:list (positive*T))(mp:PositiveMap.tree T):PositiveMap.tree T :=
  match ls with
  | nil => mp
  | (k,v)::t => map_of_list t (PositiveMap.add k v mp)
  end.

Definition key2(a x:positive) := enc_list (a::x::nil).
Definition key4(l q x r:positive) := enc_list (l::q::x::r::nil).

Definition lookup{T}(mp:PositiveMap.tree (list T))(k:positive):list T :=
  match PositiveMap.find k mp with
  | Some v => v
  | None => nil
  end.

(** successors: (a,x) -> list of b; predecessors: b -> list of (a,x) *)
Fixpoint succ_map(E:list (positive*positive*positive))(mp:PositiveMap.tree (list positive)) :=
  match E with
  | nil => mp
  | (a,x,b)::t => succ_map t (PositiveMap.add (key2 a x) (b::lookup mp (key2 a x)) mp)
  end.

Fixpoint pred_map(E:list (positive*positive*positive))(mp:PositiveMap.tree (list (positive*positive))) :=
  match E with
  | nil => mp
  | (a,x,b)::t => pred_map t (PositiveMap.add b ((a,x)::lookup mp b) mp)
  end.

Fixpoint C_set(C:list (positive*positive*positive*positive))(mp:PositiveMap.tree unit) :=
  match C with
  | nil => mp
  | (l,q,x,r)::t => C_set t (PositiveMap.add (key4 l q x r) tt mp)
  end.

(** labels standing for symbol `i` (resp. controls standing for state `s0`) *)
Definition labels_in(xm:PositiveMap.tree Σ)(X:list (positive*Σ))(i:Σ):list positive :=
  filter (fun x => match PositiveMap.find x xm with Some j => Σ_eqb i j | None => false end) (map fst X).
Definition controls_in(qm:PositiveMap.tree St)(Q:list (positive*St))(s0:St):list positive :=
  filter (fun q => match PositiveMap.find q qm with Some s1 => St_eqb s0 s1 | None => false end) (map fst Q).

(** each table is computed once (call-by-value) and then only looked up *)
Definition mk_labels xm X : Σ -> list positive :=
  let l0 := labels_in xm X Σ0 in
  let l1 := labels_in xm X Σ1 in
  let l2 := labels_in xm X Σ2 in
  let l3 := labels_in xm X Σ3 in
  fun i => match i with Σ0 => l0 | Σ1 => l1 | Σ2 => l2 | Σ3 => l3 end.
Definition mk_controls qm Q : St -> list positive :=
  let c0 := controls_in qm Q St0 in
  let c1 := controls_in qm Q St1 in
  fun s0 => match s0 with St0 => c0 | St1 => c1 end.

(* End: lookup structures *)

Section ClosedAut.

Hypothesis tm:TM Σ.
Hypothesis c:AutCert.

(* Begin: precomputed tables, see `check_aut` below *)

Hypothesis xm:PositiveMap.tree Σ.
Hypothesis qm:PositiveMap.tree St.
Definition sym(x:positive):option Σ := PositiveMap.find x xm.
Definition ctl(q:positive):option St := PositiveMap.find q qm.
Hypothesis labels_of: Σ -> list positive.
Hypothesis labels_of_spec: forall i x, In x (labels_of i) -> sym x = Some i.
Hypothesis controls_of: St -> list positive.
Hypothesis controls_of_spec: forall s0 q, In q (controls_of s0) -> ctl q = Some s0.
Hypothesis SL SR:PositiveMap.tree (list positive).
Hypothesis SL_spec: forall a x b, In b (lookup SL (key2 a x)) -> In (a,x,b) c.(ac_EL).
Hypothesis SR_spec: forall a x b, In b (lookup SR (key2 a x)) -> In (a,x,b) c.(ac_ER).
Hypothesis PL PR:PositiveMap.tree (list (positive*positive)).
Hypothesis PL_spec: forall a x b, In (a,x,b) c.(ac_EL) -> In (a,x) (lookup PL b).
Hypothesis PR_spec: forall a x b, In (a,x,b) c.(ac_ER) -> In (a,x) (lookup PR b).
Hypothesis CS:PositiveMap.tree unit.
Hypothesis CS_spec: forall l q x r, PositiveMap.find (key4 l q x r) CS = Some tt -> In (l,q,x,r) c.(ac_C).

Definition memC(l q x r:positive):bool :=
  match PositiveMap.find (key4 l q x r) CS with
  | Some _ => true
  | None => false
  end.

Definition mem_pos(p:positive)(ls:list positive):bool := existsb (Pos.eqb p) ls.

(* End: precomputed tables *)


(* Begin: checks *)

(** every blank state is entered from a blank state by a Σ0 cell *)
Definition check_cyc(P:PositiveMap.tree (list (positive*positive)))(Cy:list positive):bool :=
  forallb (fun b =>
    existsb (fun (ax:positive*positive) =>
      let (a,x):=ax in
      mem_pos a Cy &&&
      match sym x with Some Σ0 => true | _ => false end) (lookup P b)) Cy.

(** states reached after reading a side (nearest cell first in the list) *)
Fixpoint ends(S:PositiveMap.tree (list positive))(Cy:list positive)(w:list Σ):list positive :=
  match w with
  | nil => Cy
  | h::t => flat_map (fun a => flat_map (fun x => lookup S (key2 a x)) (labels_of h)) (ends S Cy t)
  end.

Definition check_start:bool :=
  let el := ends SL c.(ac_CL) Start_l in
  let er := ends SR c.(ac_CR) Start_r in
  existsb (fun (cf:positive*positive*positive*positive) =>
    match cf with
    | (l,q,x,r) =>
      mem_pos l el &&& mem_pos r er &&&
      match ctl q, sym x with
      | Some St0, Some Σ1 => true
      | _,_ => false
      end
    end) c.(ac_C).

Definition check_cfg(cf:positive*positive*positive*positive):bool :=
  match cf with
  | (l,q,x,r) =>
    match ctl q, sym x with
    | Some s0, Some i0 =>
      match tm s0 i0 with
      | Some {| nxt:=s1; dir:=d; out:=o |} =>
        existsb (fun x' =>
        existsb (fun q' =>
          match d with
          | Dpos =>
            existsb (fun l2 =>
              forallb (fun (ry:positive*positive) => let (r2,y):=ry in memC l2 q' y r2) (lookup PR r))
            (lookup SL (key2 l x'))
          | Dneg =>
            existsb (fun r2 =>
              forallb (fun (ly:positive*positive) => let (l2,y):=ly in memC l2 q' y r2) (lookup PL l))
            (lookup SR (key2 r x'))
          end) (controls_of s1)) (labels_of o)
      | None => false
      end
    | _,_ => false
    end
  end.

Definition check_all:bool :=
  check_cyc PL c.(ac_CL) &&&
  check_cyc PR c.(ac_CR) &&&
  check_start &&&
  forallb check_cfg c.(ac_C).

(* End: checks *)

(* Begin: proofs *)














Lemma memC_spec l q x r:
  memC l q x r = true -> In (l,q,x,r) c.(ac_C).
Proof.
  unfold memC.
  destruct (PositiveMap.find (key4 l q x r) CS) as [[]|] eqn:E. 2: cg.
  intros _.
  apply CS_spec,E.
Qed.

Lemma mem_pos_spec p ls:
  mem_pos p ls = true -> In p ls.
Proof.
  unfold mem_pos.
  rewrite existsb_exists.
  intros [p0 [H0 H1]].
  rewrite Pos.eqb_eq in H1. subst. apply H0.
Qed.

(** paths over a side, read from far away towards the head *)
Inductive Path(E:list (positive*positive*positive))(Cy:list positive): list Σ -> positive -> Prop :=
| Path_nil a: In a Cy -> Path E Cy nil a
| Path_cons h t a x b: Path E Cy t a -> In (a,x,b) E -> sym x = Some h -> Path E Cy (h::t) b.

Definition Covered(es:ListES):Prop :=
  exists l q x r,
    In (l,q,x,r) c.(ac_C) /\
    ctl q = Some es.(List_Tape.s) /\
    sym x = Some es.(List_Tape.m) /\
    Path c.(ac_EL) c.(ac_CL) es.(List_Tape.l) l /\
    Path c.(ac_ER) c.(ac_CR) es.(List_Tape.r) r.

Lemma ends_spec S E Cy w b:
  (forall a x b, In b (lookup S (key2 a x)) -> In (a,x,b) E) ->
  In b (ends S Cy w) -> Path E Cy w b.
Proof.
  intro HS.
  gd b.
  induction w as [|h t]; intros b H.
  - ctor. apply H.
  - cbn in H.
    rewrite in_flat_map in H.
    destruct H as [a [H0 H1]].
    rewrite in_flat_map in H1.
    destruct H1 as [x [H1 H2]].
    ector.
    + apply IHt,H0.
    + apply HS,H2.
    + apply labels_of_spec,H1.
Qed.

Lemma check_cyc_spec P E Cy b:
  (forall a x b, In (a,x,b) E -> In (a,x) (lookup P b)) ->
  check_cyc P Cy = true ->
  In b Cy ->
  exists a x, In (a,x) (lookup P b) /\ In a Cy /\ sym x = Some Σ0.
Proof.
  intros HP H H0.
  unfold check_cyc in H.
  rewrite forallb_forall in H.
  specialize (H b H0).
  rewrite existsb_exists in H.
  destruct H as [[a x] [H1 H2]].
  exists a. exists x.
  split. 1: apply H1.
  destruct (mem_pos a Cy) eqn:E1. 2: cg.
  split. 1: apply mem_pos_spec,E1.
  destruct (sym x) as [[]|]; cg.
Qed.

Lemma Covered_start:
  check_start = true -> Covered StartListES.
Proof.
  unfold check_start.
  rewrite existsb_exists.
  intros [[[[l q] x] r] [H0 H1]].
  destruct (mem_pos l (ends SL (ac_CL c) Start_l)) eqn:E1. 2: cg.
  destruct (mem_pos r (ends SR (ac_CR c) Start_r)) eqn:E2. 2: cg.
  exists l. exists q. exists x. exists r.
  repeat split.
  - apply H0.
  - destruct (ctl q) as [[]|]; destruct (sym x) as [[]|]; cg; reflexivity.
  - destruct (ctl q) as [[]|]; destruct (sym x) as [[]|]; cg; reflexivity.
  - apply (ends_spec SL). 1: apply SL_spec.
    apply mem_pos_spec,E1.
  - apply (ends_spec SR). 1: apply SR_spec.
    apply mem_pos_spec,E2.
Qed.

Lemma Covered_step es:
  check_cyc PL c.(ac_CL) = true ->
  check_cyc PR c.(ac_CR) = true ->
  forallb check_cfg c.(ac_C) = true ->
  Covered es ->
  exists es', ListES_step tm es = Some es' /\ Covered es'.
Proof.
  intros HcL HcR Hcl Hcov.
  destruct Hcov as [l [q [x [r [H0 [H1 [H2 [H3 H4]]]]]]]].
  rewrite forallb_forall in Hcl.
  specialize (Hcl _ H0).
  unfold check_cfg in Hcl.
  rewrite H1,H2 in Hcl.
  destruct es as [L R m0 s0].
  cbn in H1,H2,H3,H4.
  unfold ListES_step.
  destruct (tm s0 m0) as [[s1 d o]|] eqn:Etm; cbn in Hcl; rewrite Etm in Hcl. 2: cg.
  rewrite existsb_exists in Hcl.
  destruct Hcl as [x' [Hx' Hcl]].
  rewrite existsb_exists in Hcl.
  destruct Hcl as [q' [Hq' Hcl]].
  apply labels_of_spec in Hx'.
  apply controls_of_spec in Hq'.
  destruct d.
  - (* left move *)
    rewrite existsb_exists in Hcl.
    destruct Hcl as [r2 [Hr2 Hcl]].
    apply SR_spec in Hr2.
    rewrite forallb_forall in Hcl.
    eexists. split. 1: reflexivity.
    destruct L as [|h t].
    + inversion H3 as [a0 Hin|]; subst.
      destruct (check_cyc_spec PL _ _ _ PL_spec HcL Hin) as [a [y [Ha [Ha' Hy]]]].
      specialize (Hcl _ Ha). cbn in Hcl.
      exists a. exists q'. exists y. exists r2.
      repeat split; cbn; auto 1.
      * apply memC_spec,Hcl.
      * ctor. apply Ha'.
      * ector; eauto 1.
    + inversion H3 as [|h0 t0 a x0 b0 Hp Hin Hs]; subst.
      specialize (Hcl _ (PL_spec _ _ _ Hin)). cbn in Hcl.
      exists a. exists q'. exists x0. exists r2.
      repeat split; cbn; auto 1.
      * apply memC_spec,Hcl.
      * ector; eauto 1.
  - (* right move *)
    rewrite existsb_exists in Hcl.
    destruct Hcl as [l2 [Hl2 Hcl]].
    apply SL_spec in Hl2.
    rewrite forallb_forall in Hcl.
    eexists. split. 1: reflexivity.
    destruct R as [|h t].
    + inversion H4 as [a0 Hin|]; subst.
      destruct (check_cyc_spec PR _ _ _ PR_spec HcR Hin) as [a [y [Ha [Ha' Hy]]]].
      specialize (Hcl _ Ha). cbn in Hcl.
      exists l2. exists q'. exists y. exists a.
      repeat split; cbn; auto 1.
      * apply memC_spec,Hcl.
      * ector; eauto 1.
      * ctor. apply Ha'.
    + inversion H4 as [|h0 t0 a x0 b0 Hp Hin Hs]; subst.
      specialize (Hcl _ (PR_spec _ _ _ Hin)). cbn in Hcl.
      exists l2. exists q'. exists x0. exists a.
      repeat split; cbn; auto 1.
      * apply memC_spec,Hcl.
      * ector; eauto 1.
Qed.

Lemma check_all_spec:
  check_all = true -> ~HaltsFromStart tm.
Proof.
  unfold check_all.
  intro H.
  destruct (check_cyc PL (ac_CL c)) eqn:E1. 2: cg.
  destruct (check_cyc PR (ac_CR c)) eqn:E2. 2: cg.
  destruct check_start eqn:E3. 2: cg.
  assert (Hrun: forall n, exists es, Covered es /\ Steps Σ tm n StartES (ListES_toES es)). {
    intro n.
    induction n.
    - exists StartListES.
      split.
      + apply Covered_start,E3.
      + rewrite ListES_toES_Start. ctor.
    - destruct IHn as [es [H0 H1]].
      destruct (Covered_step es E1 E2 H H0) as [es' [H2 H3]].
      exists es'.
      split. 1: apply H3.
      ector. 1: apply H1.
      rewrite ListES_step_spec,H2.
      reflexivity.
  }
  unfold HaltsFromStart.
  rewrite <-NonHalt_iff.
  intro n.
  destruct (Hrun n) as [es [_ H0]].
  eexists. apply H0.
Qed.

(* End: proofs *)

End ClosedAut.

(* Begin: tables and their specs *)

Lemma find_map_of_list{T} ls mp k (v:T):
  PositiveMap.find k (map_of_list ls mp) = Some v ->
  In (k,v) ls \/ PositiveMap.find k mp = Some v.
Proof.
  gd mp.
  induction ls as [|[k0 v0] t]; intros mp H.
  1: right; apply H.
  cbn [map_of_list] in H.
  destruct (IHt _ H) as [H0|H0].
  1: left; right; apply H0.
  rewrite PositiveMapAdditionalFacts.gsspec in H0.
  revert H0.
  destruct (PositiveMap.E.eq_dec k k0); intro H0.
  - subst. invst H0. left. left. reflexivity.
  - right. apply H0.
Qed.

Lemma key2_inj a1 x1 a2 x2:
  key2 a1 x1 = key2 a2 x2 -> a1 = a2 /\ x1 = x2.
Proof.
  unfold key2. intro H.
  apply enc_list_inj in H.
  invst H. tauto.
Qed.

Lemma key4_inj l1 q1 x1 r1 l2 q2 x2 r2:
  key4 l1 q1 x1 r1 = key4 l2 q2 x2 r2 -> l1 = l2 /\ q1 = q2 /\ x1 = x2 /\ r1 = r2.
Proof.
  unfold key4. intro H.
  apply enc_list_inj in H.
  invst H. tauto.
Qed.

Lemma succ_map_spec E mp a x b:
  In b (lookup (succ_map E mp) (key2 a x)) ->
  In (a,x,b) E \/ In b (lookup mp (key2 a x)).
Proof.
  gd mp.
  induction E as [|[[a0 x0] b0] t]; intros mp H.
  1: right; apply H.
  cbn [succ_map] in H.
  destruct (IHt _ H) as [H0|H0].
  1: left; right; apply H0.
  unfold lookup in H0.
  rewrite PositiveMapAdditionalFacts.gsspec in H0.
  revert H0.
  destruct (PositiveMap.E.eq_dec (key2 a x) (key2 a0 x0)) as [E0|E0]; intro H0.
  - destruct (key2_inj _ _ _ _ E0); subst.
    destruct H0 as [H0|H0].
    + subst. left. left. reflexivity.
    + right. apply H0.
  - right. apply H0.
Qed.

Lemma pred_map_spec E mp a x b:
  In (a,x,b) E \/ In (a,x) (lookup mp b) ->
  In (a,x) (lookup (pred_map E mp) b).
Proof.
  gd mp.
  induction E as [|[[a0 x0] b0] t]; intros mp H.
  - destruct H as [H|H]. 1: destruct H. apply H.
  - cbn [pred_map].
    apply IHt.
    destruct H as [[H|H]|H].
    + invst H. right.
      unfold lookup. rewrite PositiveMap.gss. left. reflexivity.
    + left. apply H.
    + right.
      unfold lookup. rewrite PositiveMapAdditionalFacts.gsspec.
      destruct (PositiveMap.E.eq_dec b b0).
      * subst. right. apply H.
      * apply H.
Qed.

Lemma C_set_spec C mp l q x r:
  PositiveMap.find (key4 l q x r) (C_set C mp) = Some tt ->
  In (l,q,x,r) C \/ PositiveMap.find (key4 l q x r) mp = Some tt.
Proof.
  gd mp.
  induction C as [|[[[l0 q0] x0] r0] t]; intros mp H.
  1: right; apply H.
  cbn [C_set] in H.
  destruct (IHt _ H) as [H0|H0].
  1: left; right; apply H0.
  rewrite PositiveMapAdditionalFacts.gsspec in H0.
  revert H0.
  destruct (PositiveMap.E.eq_dec (key4 l q x r) (key4 l0 q0 x0 r0)) as [E0|E0]; intro H0.
  - destruct (key4_inj _ _ _ _ _ _ _ _ E0) as [? [? [? ?]]]; subst.
    left. left. reflexivity.
  - right. apply H0.
Qed.

Lemma labels_in_spec xm X i x:
  In x (labels_in xm X i) -> PositiveMap.find x xm = Some i.
Proof.
  unfold labels_in.
  rewrite filter_In.
  intros [_ H].
  destruct (PositiveMap.find x xm) as [j|]; cg.
  pose proof (Σ_eqb_spec i j).
  destruct (Σ_eqb i j); cg.
Qed.

Lemma controls_in_spec qm Q s0 q:
  In q (controls_in qm Q s0) -> PositiveMap.find q qm = Some s0.
Proof.
  unfold controls_in.
  rewrite filter_In.
  intros [_ H].
  destruct (PositiveMap.find q qm) as [s1|]; cg.
  pose proof (St_eqb_spec s0 s1).
  destruct (St_eqb s0 s1); cg.
Qed.

Lemma mk_labels_spec xm X i x:
  In x (mk_labels xm X i) -> PositiveMap.find x xm = Some i.
Proof.
  destruct i; apply labels_in_spec.
Qed.

Lemma mk_controls_spec qm Q s0 q:
  In q (mk_controls qm Q s0) -> PositiveMap.find q qm = Some s0.
Proof.
  destruct s0; apply controls_in_spec.
Qed.

Lemma succ_map_empty_spec E a x b:
  In b (lookup (succ_map E (PositiveMap.empty _)) (key2 a x)) -> In (a,x,b) E.
Proof.
  intro H.
  destruct (succ_map_spec _ _ _ _ _ H) as [H0|H0]. 1: apply H0.
  unfold lookup in H0. rewrite PositiveMap.gempty in H0. destruct H0.
Qed.

Lemma pred_map_empty_spec E a x b:
  In (a,x,b) E -> In (a,x) (lookup (pred_map E (PositiveMap.empty _)) b).
Proof.
  intro H. apply pred_map_spec. left. apply H.
Qed.

Lemma C_set_empty_spec C l q x r:
  PositiveMap.find (key4 l q x r) (C_set C (PositiveMap.empty _)) = Some tt -> In (l,q,x,r) C.
Proof.
  intro H.
  destruct (C_set_spec _ _ _ _ _ _ H) as [H0|H0]. 1: apply H0.
  rewrite PositiveMap.gempty in H0. cg.
Qed.

(* End: tables and their specs *)

(** The checker: builds every table once, then runs `check_all`. *)
Definition check_aut(tm:TM Σ)(c:AutCert):bool :=
  let xm := map_of_list c.(ac_X) (PositiveMap.empty _) in
  let qm := map_of_list c.(ac_Q) (PositiveMap.empty _) in
  check_all tm c xm qm (mk_labels xm c.(ac_X)) (mk_controls qm c.(ac_Q))
    (succ_map c.(ac_EL) (PositiveMap.empty _)) (succ_map c.(ac_ER) (PositiveMap.empty _))
    (pred_map c.(ac_EL) (PositiveMap.empty _)) (pred_map c.(ac_ER) (PositiveMap.empty _))
    (C_set c.(ac_C) (PositiveMap.empty _)).

Lemma check_aut_spec tm c:
  check_aut tm c = true -> ~HaltsFromStart tm.
Proof.
  unfold check_aut. cbv zeta.
  intro H.
  eapply check_all_spec.
  8: apply H.
  - intros. apply (mk_labels_spec _ _ _ _ H0).
  - intros. apply (mk_controls_spec _ _ _ _ H0).
  - apply succ_map_empty_spec.
  - apply succ_map_empty_spec.
  - apply pred_map_empty_spec.
  - apply pred_map_empty_spec.
  - apply C_set_empty_spec.
Qed.

Definition closed_aut_decider(c:AutCert):HaltDecider :=
  fun tm => if check_aut tm c then Result_NonHalt else Result_Unknown.

Lemma closed_aut_decider_spec c BB:
  HaltDecider_WF BB (closed_aut_decider c).
Proof.
  intro tm.
  unfold closed_aut_decider.
  pose proof (check_aut_spec tm c).
  destruct (check_aut tm c); tauto.
Qed.
