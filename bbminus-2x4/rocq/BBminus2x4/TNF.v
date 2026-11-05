Require Import List.
Require Import Lia.
Require Import ZArith.

From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import BB2x4_Make_TM.
From BBminus2x4 Require Import List_Routines.
From BBminus2x4 Require Import BB2x4_Deciders_Generic.
From BBminus2x4 Require Import Prelims.
From BBminus2x4 Require Import Tactics.
From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import BB2x4_Encodings.

From BBminus2x4 Require Import Deciders_Common.

Section TNF.

Definition CountHaltTrans tm :=
  list_nat_sum (map (fun s=>list_nat_sum (map (fun i => isHaltTrans (tm s i)) Σ_list)) St_list).

Lemma CountHaltTrans_upd {tm s i} tr:
  tm s i = None ->
  S (CountHaltTrans (TM_upd Σ Σ_eqb tm s i (Some tr))) =
  (CountHaltTrans tm).
Proof.
  unfold CountHaltTrans.
  cbn.
  unfold TM_upd.
  intro H.
  destruct s,i; cbn; rewrite H; cbn; lia.
Qed.

Lemma CountHaltTrans_0_NonHalt {tm st}:
  CountHaltTrans tm = 0 ->
  ~Halts Σ tm st.
Proof.
  intro H.
  assert (forall s i, tm s i <> None). {
    intros.
    unfold CountHaltTrans in H.
    cbn in H.
    repeat rewrite Nat.eq_add_0 in H.
    repeat rewrite isHaltTrans_0 in H.
    repeat destruct_and.
    destruct s,i; assumption.
  }
  intro H1.
  unfold Halts,HaltsAt in H1.
  destruct H1 as [n [st' [H1 H2]]].
  destruct st'. cbn in H2.
  destruct (tm s (σ 0%Z)) eqn:E; cg.
  destruct t. cg.
Qed.

Record TNF_Node := {
  TNF_tm: TM Σ;
  TNF_cnt: nat;
  TNF_ptr: St;
}.

Definition TNF_Node_WF(x:TNF_Node):Prop :=
  let (tm,cnt,ptr) := x in
  cnt = CountHaltTrans tm /\
  cnt <> 0 /\
  UnusedState_ptr tm ptr.

Definition St_leb s1 s2 :=
  Nat.leb (St_to_nat s2) (St_to_nat s1).

Lemma St_leb_spec s1 s2:
  if St_leb s1 s2 then St_le s1 s2 else ~(St_le s1 s2).
Proof.
  destruct (St_leb s1 s2) eqn:E.
  - unfold St_le.
    unfold St_leb in E.
    rewrite Nat.leb_le in E.
    apply E.
  - unfold St_le.
    unfold St_leb in E.
    rewrite <-Nat.leb_le.
    cg.
Qed.

Definition TM_upd' tm s i tr :=
  TM_simplify (TM_upd Σ Σ_eqb tm s i tr).

Lemma TM_upd'_spec tm s i tr:
  TM_upd' tm s i tr = TM_upd Σ Σ_eqb tm s i tr.
Proof.
  unfold TM_upd'.
  rewrite TM_simplify_spec.
  reflexivity.
Qed.

Definition TNF_Node_upd(x:TNF_Node) s i tr:=
  let (tm,cnt,ptr):=x in
  {|
    TNF_tm:=TM_upd' tm s i (Some tr);
    TNF_cnt:=Nat.pred cnt;
    TNF_ptr:=(if St_eqb ptr (nxt _ tr) then (St_suc ptr) else ptr)
  |}.

(** Symbol normalisation (new, not in Coq-BB5): Σ2 and Σ3 do not occur on the start tape.
  While no defined transition reads or writes either of them, they are interchangeable,
  so a new transition writing Σ3 is skipped in favour of the same one writing Σ2. *)
Definition Σ_is01(i:Σ):bool :=
  match i with
  | Σ0 | Σ1 => true
  | _ => false
  end.

Definition sym23_free(tm:TM Σ)(i:Σ):bool :=
  Σ_is01 i &&&
  forallb_St (fun s0 =>
  forallb_Σ (fun i0 =>
    match tm s0 i0 with
    | None => true
    | Some tr => Σ_is01 i0 &&& Σ_is01 (out _ tr)
    end)).

Definition TNF_trans_ok tm ptr i (tr:Trans Σ):bool :=
  St_leb ptr (nxt _ tr) &&&
  (negb (sym23_free tm i) ||| negb (Σ_eqb (out _ tr) Σ3)).

Definition TNF_Node_expand(x:TNF_Node) s i:=
  let (tm,cnt,ptr):=x in
  if Nat.eqb cnt 1 then nil else
    map (TNF_Node_upd x s i)
    (filter (TNF_trans_ok tm ptr i) Trans_list).

Hypothesis BB:nat.


Lemma nat_eqb_spec n1 n2 : if Nat.eqb n1 n2 then n1=n2 else n1<>n2.
Proof.
  destruct (Nat.eqb_spec n1 n2); cg.
Qed.

Ltac nat_eq_dec s1 s2 :=
  eq_dec nat_eqb_spec Nat.eqb s1 s2.

Ltac St_le_dec s1 s2 :=
  eq_dec St_leb_spec St_leb s1 s2.

Definition Σ_swap23(i:Σ):Σ :=
  match i with
  | Σ2 => Σ3
  | Σ3 => Σ2
  | _ => i
  end.

Definition Trans_swap23(tr:Trans Σ):Trans Σ :=
  {| nxt:=nxt _ tr; dir:=dir _ tr; out:=Σ_swap23 (out _ tr) |}.

(** The machine with symbols Σ2 and Σ3 exchanged. *)
Definition TM_swap23(tm:TM Σ):TM Σ :=
  fun s0 i0 =>
  match tm s0 (Σ_swap23 i0) with
  | Some tr => Some (Trans_swap23 tr)
  | None => None
  end.

Lemma TM_swap23_HF tm:
  forall (s0:St)(i0:Σ),
  match TM_swap23 tm s0 i0 with
  | Some tr =>
    let (s',d,o) := tr in
    tm s0 (Σ_swap23 i0) = Some {| nxt:=s'; dir:=d; out:= Σ_swap23 o |}
  | None => tm s0 (Σ_swap23 i0) = None
  end.
Proof.
  intros.
  unfold TM_swap23.
  destruct (tm s0 (Σ_swap23 i0)) as [[s' d o]|]; cbn.
  - destruct o; reflexivity.
  - reflexivity.
Qed.

Lemma StartTape_01 x:
  Σ_is01 (StartTape x) = true.
Proof.
  unfold StartTape.
  repeat match goal with
  | |- context [match ?y with _ => _ end] => destruct y
  end; reflexivity.
Qed.

Lemma StartES_swap23:
  F_ES Σ Σ Σ_swap23 StartES = StartES.
Proof.
  unfold StartES. cbn.
  f_equal. fext.
  pose proof (StartTape_01 x) as H.
  destruct (StartTape x); cbn in H; cg; reflexivity.
Qed.

Lemma sym23_free_spec tm i:
  sym23_free tm i = true ->
  Σ_swap23 i = i /\
  forall s0 i0 tr, tm s0 i0 = Some tr -> Σ_swap23 i0 = i0 /\ Σ_swap23 (out _ tr) = out _ tr.
Proof.
  unfold sym23_free.
  destruct (Σ_is01 i) eqn:Ei. 2: discriminate.
  intro H.
  split.
  1: destruct i; cbn in Ei; cg; reflexivity.
  rewrite forallb_St_spec in H.
  intros s0 i0 tr H0.
  specialize (H s0).
  rewrite forallb_Σ_spec in H.
  specialize (H i0).
  rewrite H0 in H.
  destruct tr as [s' d o].
  cbn.
  destruct i0; cbn in H; try discriminate.
  all: destruct o; cbn in H; try discriminate.
  all: split; reflexivity.
Qed.

Lemma HaltTimeUpperBound_LE_swap23 tm0 s0 i0 s' d:
  sym23_free tm0 i0 = true ->
  HaltTimeUpperBound _ BB StartES (LE _ (TM_upd Σ Σ_eqb tm0 s0 i0 (Some {| nxt:=s'; dir:=d; out:=Σ2 |}))) ->
  HaltTimeUpperBound _ BB StartES (LE _ (TM_upd Σ Σ_eqb tm0 s0 i0 (Some {| nxt:=s'; dir:=d; out:=Σ3 |}))).
Proof.
  intros H H0.
  destruct (sym23_free_spec _ _ H) as [Hi Hq].
  unfold HaltTimeUpperBound.
  intros tmX n0 HLE Hh.
  apply (H0 (TM_swap23 tmX) n0).
  - unfold LE.
    intros q a.
    specialize (HLE q a).
    revert HLE.
    unfold TM_upd.
    St_eq_dec q s0; Σ_eq_dec a i0; cbn; intro HLE.
    + subst. left.
      destruct HLE as [HLE|HLE]. 2: cg.
      unfold TM_swap23.
      rewrite Hi,<-HLE.
      reflexivity.
    + destruct (tm0 q a) as [tr|] eqn:E. 2: right; reflexivity.
      left.
      destruct HLE as [HLE|HLE]. 2: cg.
      destruct (Hq _ _ _ E) as [Ha Ho].
      unfold TM_swap23.
      rewrite Ha,<-HLE.
      destruct tr as [s1 d1 o1].
      unfold Trans_swap23. cbn in *. rewrite Ho. reflexivity.
    + destruct (tm0 q a) as [tr|] eqn:E. 2: right; reflexivity.
      left.
      destruct HLE as [HLE|HLE]. 2: cg.
      destruct (Hq _ _ _ E) as [Ha Ho].
      unfold TM_swap23.
      rewrite Ha,<-HLE.
      destruct tr as [s1 d1 o1].
      unfold Trans_swap23. cbn in *. rewrite Ho. reflexivity.
    + destruct (tm0 q a) as [tr|] eqn:E. 2: right; reflexivity.
      left.
      destruct HLE as [HLE|HLE]. 2: cg.
      destruct (Hq _ _ _ E) as [Ha Ho].
      unfold TM_swap23.
      rewrite Ha,<-HLE.
      destruct tr as [s1 d1 o1].
      unfold Trans_swap23. cbn in *. rewrite Ho. reflexivity.
  - eapply (F_HaltsAt Σ Σ Σ_swap23 tmX (TM_swap23 tmX)).
    1: apply TM_swap23_HF.
    rewrite StartES_swap23.
    apply Hh.
Qed.

Lemma TNF_trans_ok_St_le tm ptr i tr:
  TNF_trans_ok tm ptr i tr = true ->
  St_le ptr (nxt _ tr).
Proof.
  unfold TNF_trans_ok.
  intro H.
  pose proof (St_leb_spec ptr (nxt _ tr)) as H0.
  destruct (St_leb ptr (nxt _ tr)); cg.
Qed.

Lemma TNF_trans_ok_false tm ptr i tr:
  St_le ptr (nxt _ tr) ->
  TNF_trans_ok tm ptr i tr = false ->
  sym23_free tm i = true /\ out _ tr = Σ3.
Proof.
  unfold TNF_trans_ok.
  intros H H0.
  pose proof (St_leb_spec ptr (nxt _ tr)) as H1.
  destruct (St_leb ptr (nxt _ tr)). 2: contradiction.
  destruct (sym23_free tm i); cbn in H0. 2: cg.
  split. 1: reflexivity.
  pose proof (Σ_eqb_spec (out _ tr) Σ3) as H2.
  destruct (Σ_eqb (out _ tr) Σ3); cbn in H0; cg.
Qed.

Definition TNF_Node_HTUB(x:TNF_Node):Prop :=
  let (tm,_,_):=x in
  HaltTimeUpperBound _ BB StartES (LE _ tm).

Lemma TNF_Node_expand_spec {x:TNF_Node}{n s t}:
  HaltsAt Σ (TNF_tm x) n StartES ->
  Steps Σ (TNF_tm x) n StartES (s,t) ->
  n<=BB ->
  TNF_Node_WF x ->
  (forall x', In x' (TNF_Node_expand x s (t Z0)) -> TNF_Node_WF x') /\
  ((forall x', In x' (TNF_Node_expand x s (t Z0)) -> TNF_Node_HTUB x') -> TNF_Node_HTUB x).
Proof.
  destruct x as [tm cnt ptr]. unfold TNF_tm.
  intros.
  split.
  - intros.
    unfold TNF_Node_expand in H3.
    nat_eq_dec cnt 1.
    1: destruct H3.
    epose proof (HaltsAtES_Trans H H0) as H5.
    destruct H2 as [H2a [H2b H2c]].
    rewrite in_map_iff in H3.
    destruct H3 as [tr [H3a H3b]].
    cbn in H3a. rewrite TM_upd'_spec in H3a.
    rewrite <-H3a.
    repeat split.
    + destruct cnt; cg. unfold Nat.pred.
      epose proof (CountHaltTrans_upd tr H5) as H6.
      rewrite <-H2a in H6.
      injection H6.
      intro H7. rewrite H7. reflexivity.
    + destruct cnt; cg. unfold Nat.pred. cg.
    + eapply UnusedState_ptr_upd; eauto 1.
      rewrite filter_In in H3b.
      destruct H3b as [_ H3b].
      apply (TNF_trans_ok_St_le _ _ _ _ H3b).
  - unfold TNF_Node_HTUB.
    intros.
    destruct H2 as [H2a [H2b H2c]].
    eapply HaltTimeUpperBound_LE_HaltAtES_UnusedState_ptr; eauto 1.
    intros.
    unfold TNF_Node_expand in H3.
    nat_eq_dec cnt 1.
    + apply HaltTimeUpperBound_LE_NonHalt.
      apply CountHaltTrans_0_NonHalt.
      epose proof (HaltsAtES_Trans H H0) as H5.
      epose proof (CountHaltTrans_upd tr H5) as H6. cg.
    + assert (Hok: forall tr0, TNF_trans_ok tm ptr (t 0%Z) tr0 = true ->
        HaltTimeUpperBound Σ BB StartES (LE Σ (TM_upd Σ Σ_eqb tm s (t 0%Z) (Some tr0)))). {
        intros tr0 Htr0.
        specialize (H3 (TNF_Node_upd {| TNF_tm := tm; TNF_cnt := cnt; TNF_ptr := ptr |} s (t 0%Z) tr0)).
        rewrite <-TM_upd'_spec.
        apply H3. clear H3.
        rewrite in_map_iff. exists tr0.
        split. 1: reflexivity.
        rewrite filter_In.
        split.
        1: apply Trans_list_spec.
        apply Htr0.
      }
      destruct (TNF_trans_ok tm ptr (t 0%Z) tr) eqn:Etr.
      1: apply Hok,Etr.
      destruct (TNF_trans_ok_false _ _ _ _ H2 Etr) as [Hfree Hout].
      destruct tr as [s1 d1 o1].
      cbn in Hout. subst o1.
      apply HaltTimeUpperBound_LE_swap23. 1: apply Hfree.
      apply Hok.
      unfold TNF_trans_ok. cbn.
      pose proof (St_leb_spec ptr s1) as H6.
      cbn in H2.
      destruct (St_leb ptr s1). 2: contradiction.
      destruct (sym23_free tm (t 0%Z)); reflexivity.
Qed.

Lemma TNF_Node_NonHalt {x:TNF_Node}:
  ~ HaltsFromStart (TNF_tm x) ->
  TNF_Node_HTUB x.
Proof.
  destruct x as [tm cnt ptr].
  intros. cbn.
  apply HaltTimeUpperBound_LE_NonHalt,H.
Qed.

Definition SearchQueue :=
  ((list TNF_Node)*(list TNF_Node))%type.

Definition SearchQueue_WF (q:SearchQueue) x0:=
  let (q1,q2):=q in
  (forall x, In x (q1++q2) -> TNF_Node_WF x) /\
  ((forall x, In x (q1++q2) -> TNF_Node_HTUB x) -> TNF_Node_HTUB x0).

(**
The following two definitions are needed for printing purpose: the OCaml extraction will insert print statements
in place of these definitions. See the extraction folder.
**)
Definition node_halt (h : TNF_Node) (decider_id: DeciderIdentifier) {A} : A -> A := fun a => a.
Definition node_nonhalt (h : TNF_Node) (decider_id: DeciderIdentifier) {A} : A -> A := fun a => a.

Definition SearchQueue_upd(q:SearchQueue)(f:HaltDeciderWithIdentifier) :=
  match q with
  | (h::t,q2) =>
    let res := f (TNF_tm h) in
    let decider_id := snd res in
    match fst res with
    | Result_Halt s i => node_halt h decider_id (TNF_Node_expand h s i ++ t, q2)
    | Result_NonHalt => node_nonhalt h decider_id (t, q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.

Lemma SearchQueue_upd_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upd q f) x0.
Proof.
  destruct q as [q1 q2].
  destruct q1 as [|h q1].
  1: tauto.
  cbn.
  intros Hq Hf.
  destruct Hq as [Hq1 Hq2].
  specialize (Hf (TNF_tm h)).
  destruct (fst (f (TNF_tm h))).
  - cbn.
    split.
    + intros.
      repeat rewrite in_app_iff in H.
      rewrite or_assoc in H.
      rewrite <-in_app_iff in H.
      destruct H.
      2: apply Hq1; tauto.
      destruct Hf as [n [t [Hf1 [Hf2 [Hf3 Hf4]]]]].
      subst.
      eapply TNF_Node_expand_spec; eauto 1.
      apply Hq1. tauto.
    + intros. apply Hq2. intros.
      destruct H0.
      * subst.
        destruct Hf as [n [t [Hf1 [Hf2 [Hf3 Hf4]]]]].
        eapply TNF_Node_expand_spec; eauto 1.
        1: apply Hq1; tauto.
        intros.
        apply H.
        subst.
        repeat rewrite in_app_iff.
        tauto.
      * apply H.
        repeat rewrite in_app_iff.
        rewrite in_app_iff in H0.
        tauto.
  - split.
    + intros; apply Hq1; tauto.
    + intros; apply Hq2. intros.
      destruct H0. 2: auto 2.
      subst.
      apply TNF_Node_NonHalt,Hf.
  - split.
    + intros. apply Hq1.
      rewrite in_app_iff.
      rewrite in_app_iff in H. cbn in H.
      tauto.
    + intros. apply Hq2. intros. apply H.
      rewrite in_app_iff.
      rewrite in_app_iff in H0. cbn.
      tauto.
Qed.

Definition SearchQueue_upd_bfs(q:SearchQueue)(f:HaltDeciderWithIdentifier) :=
  match q with
  | (h::t,q2) =>
    match fst (f (TNF_tm h)) with
    | Result_Halt s i => (t,(TNF_Node_expand h s i)++q2)
    | Result_NonHalt => (t,q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.

Lemma SearchQueue_upd_bfs_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upd_bfs q f) x0.
Proof.
  intros.
  pose proof (SearchQueue_upd_spec H H0).
  unfold SearchQueue_WF.
  unfold SearchQueue_upd_bfs.
  unfold SearchQueue_WF in H1.
  unfold SearchQueue_upd in H1.
  destruct q as [q1 q2].
  destruct q1 as [|h t].
  1: apply H1.
  destruct (fst (f (TNF_tm h))); auto 1.
  assert (
    forall x, In x ((TNF_Node_expand h s i ++ t) ++ q2) <-> In x (t ++ TNF_Node_expand h s i ++ q2)
  ). {
  intros.
  repeat rewrite in_app_iff.
  tauto.
  }
  split.
  - intro. rewrite <-H2.
    apply H1.
  - intro. apply H1.
    intros.
    apply H3; auto 1.
    rewrite <-H2.
    apply H4.
Qed.

Definition SearchQueue_reset(q:SearchQueue):SearchQueue :=
  match q with
  | (q1,q2) => (q1++q2,nil)
  end.

Lemma SearchQueue_reset_spec {q x0}:
  SearchQueue_WF q x0 ->
  SearchQueue_WF (SearchQueue_reset q) x0.
Proof.
  unfold SearchQueue_WF,SearchQueue_reset.
  destruct q as [q1 q2].
  intro.
  split.
  - intros. apply H.
    rewrite app_nil_r in H0. apply H0.
  - intros. apply H.
    intros. apply H0. rewrite app_nil_r. apply H1.
Qed.

Definition SearchQueue_init(x0:TNF_Node):SearchQueue := (x0::nil,nil).

Definition SearchQueue_init_spec(x0:TNF_Node):
  TNF_Node_WF x0 ->
  SearchQueue_WF (SearchQueue_init x0) x0.
Proof.
  intro.
  unfold SearchQueue_WF,SearchQueue_init.
  cbn.
  split.
  - intros. destruct H0 as [H0|[]]; cg.
  - intros. apply H0. tauto.
Qed.

Fixpoint SearchQueue_upds q f (n:nat) :=
match (fst q) with
| nil => q
| _ =>
  match n with
  | O => SearchQueue_upd q f
  | S n0 => SearchQueue_upds (SearchQueue_upds q f n0) f n0
  end
end.

Lemma SearchQueue_upds_spec q x0 f n:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upds q f n) x0.
Proof.
  intros.
  gd q.
  induction n; cbn; intros.
  - destruct (fst q); auto 1.
    eapply SearchQueue_upd_spec; eauto 1.
  - destruct (fst q); auto 1.
    apply IHn,IHn,H.
Qed.

Fixpoint SearchQueue_upds_bfs q f (n:nat) :=
  match n with
  | O => q
  | S n0 => SearchQueue_upd_bfs (SearchQueue_upds_bfs q f n0) f
  end.

Lemma SearchQueue_upds_bfs_spec q x0 f n:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upds_bfs q f n) x0.
Proof.
  intros.
  gd q.
  induction n; cbn; intros; auto 1.
  apply SearchQueue_upd_bfs_spec; auto 1.
  apply IHn,H.
Qed.

Definition SearchQueue_bfs q f :=
  SearchQueue_reset (SearchQueue_upds_bfs q f (length (fst q))).

Lemma SearchQueue_bfs_spec q x0 f:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_bfs q f) x0.
Proof.
  intros.
  unfold SearchQueue_bfs.
  apply SearchQueue_reset_spec.
  apply SearchQueue_upds_bfs_spec; auto 1.
Qed.

End TNF.