(** Tree Normal Form enumeration from the start tape `110[1]011`: shared definitions and the lemma that turns
  an emptied search queue into a halting-time bound. The enumeration itself is split into the subtrees below
  the root (one file per subtree in `TNF_Roots/`, compiled in parallel) and assembled in `TNF_Enumeration.v`.

  Differences from Coq-BB5's `BB2x4_TNF_Enumeration.v`: the root machine halts at once (it reads Σ1 in state A),
  so the first expansion fills (A,Σ1) and not (A,Σ0); no left/right reduction is applied (the
  `first_trans_is_R` filter is gone); symbols Σ2/Σ3 are normalised in `TNF.v`. *)

Require Import Lia.
Require Import List.
Require Import ZArith.

From BBminus2x4 Require Import TNF.
From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import Deciders_Common.
From BBminus2x4 Require Import Tactics.
From BBminus2x4 Require Import BB2x4_Encodings.
From BBminus2x4 Require Import Prelims.
From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import BB2x4_Deciders_Pipeline.

Definition TM0: TM Σ :=
  fun x i => None.

Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 14).

Definition BB := N.to_nat BBinit_minus_one.

Lemma UnusedState_TM0 s1:
  UnusedState TM0 s1 <->
  s1 <> St0.
Proof.
split; intro.
- intro H0. subst.
  destruct H as [H [H0 H1]].
  contradiction.
- repeat split; auto 1.
Qed.

Lemma root_WF: TNF_Node_WF root.
Proof.
  repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  rewrite UnusedState_TM0.
  destruct s0; unfold St_le; cbn; split; intro; cg; lia.
Qed.

Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma iter_q_suc_WF x n:
  TNF_Node_WF x ->
  SearchQueue_WF BB (Nat.iter n q_suc (SearchQueue_init x)) x.
Proof.
  intro H.
  induction n.
  - apply SearchQueue_init_spec,H.
  - replace (Nat.iter (S n) q_suc (SearchQueue_init x)) with (q_suc (Nat.iter n q_suc (SearchQueue_init x))) by (apply iter_S; reflexivity).
    remember (Nat.iter n q_suc (SearchQueue_init x)) as q.
    clear Heqq.
    unfold q_suc.
    apply SearchQueue_upds_spec.
    + apply IHn.
    + apply decider_all_spec.
Qed.

(** If the search queue started at `x` is empty after `n` rounds, every extension of `x` that halts from the
  start tape halts within `BB` steps (Coq-BB5's `HaltsAt` convention, one less than `HaltsAtPlusOne`). *)
Lemma subtree_HTUB x n:
  TNF_Node_WF x ->
  Nat.iter n q_suc (SearchQueue_init x) = (nil,nil) ->
  TNF_Node_HTUB BB x.
Proof.
  intros H H0.
  pose proof (iter_q_suc_WF x n H) as H1.
  rewrite H0 in H1.
  apply H1.
  cbn. intros. contradiction.
Qed.

(** Splitting the tree into subtrees: `node_at p` is the node reached from the root by the child indices `p`,
  where the children of a node are those produced when the pipeline reports that it halts. *)
Definition expand_halt(x:TNF_Node):list TNF_Node :=
  match fst (decider_all (TNF_tm x)) with
  | Result_Halt s i => TNF_Node_expand x s i
  | _ => nil
  end.

Definition is_halt(r:HaltDecideResult):bool :=
  match r with
  | Result_Halt _ _ => true
  | _ => false
  end.

Definition node_at(p:list nat):TNF_Node :=
  fold_left (fun x j => nth j (expand_halt x) root) p root.

Lemma node_at_app p j:
  node_at (p++j::nil) = nth j (expand_halt (node_at p)) root.
Proof.
  unfold node_at.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma expand_halt_WF x y:
  TNF_Node_WF x -> In y (expand_halt x) -> TNF_Node_WF y.
Proof.
  intros H H0.
  unfold expand_halt in H0.
  pose proof (decider_all_spec (TNF_tm x)) as H1.
  destruct (decider_all (TNF_tm x)) as [r id].
  cbn in H0,H1.
  destruct r as [s i| |]; try destruct H0.
  destruct H1 as [n [t [H1 [H2 [H3 H4]]]]].
  subst i.
  eapply (TNF_Node_expand_spec BB H1 H2 H4 H).
  apply H0.
Qed.

Lemma expand_halt_HTUB x:
  TNF_Node_WF x ->
  is_halt (fst (decider_all (TNF_tm x))) = true ->
  (forall y, In y (expand_halt x) -> TNF_Node_HTUB BB y) ->
  TNF_Node_HTUB BB x.
Proof.
  intros H H0 H1.
  unfold expand_halt in H1.
  pose proof (decider_all_spec (TNF_tm x)) as H2.
  destruct (decider_all (TNF_tm x)) as [r id].
  cbn in H0,H1,H2.
  destruct r as [s i| |]; cbn in H0; cg.
  destruct H2 as [n [t [H2 [H3 [H4 H5]]]]].
  subst i.
  apply (TNF_Node_expand_spec BB H2 H3 H5 H).
  apply H1.
Qed.

Lemma node_at_WF p:
  TNF_Node_WF (node_at p).
Proof.
  induction p as [|j p] using rev_ind.
  1: apply root_WF.
  rewrite node_at_app.
  destruct (Nat.lt_ge_cases j (length (expand_halt (node_at p)))) as [H|H].
  - eapply expand_halt_WF. 1: apply IHp.
    apply nth_In,H.
  - rewrite nth_overflow. 2: apply H.
    apply root_WF.
Qed.

(** A leaf of the split: the search queue started at `node_at p` empties within `n` rounds. *)
Lemma leaf_HTUB p n:
  Nat.iter n q_suc (SearchQueue_init (node_at p)) = (nil,nil) ->
  TNF_Node_HTUB BB (node_at p).
Proof.
  apply subtree_HTUB,node_at_WF.
Qed.

(** An inner node of the split: the pipeline reports that it halts, and all its `k` children are bounded. *)
Lemma inner_HTUB p k:
  is_halt (fst (decider_all (TNF_tm (node_at p)))) = true ->
  length (expand_halt (node_at p)) = k ->
  (forall j, j < k -> TNF_Node_HTUB BB (node_at (p++j::nil))) ->
  TNF_Node_HTUB BB (node_at p).
Proof.
  intros H H0 H1.
  apply expand_halt_HTUB. 1: apply node_at_WF. 1: apply H.
  intros y Hy.
  apply (In_nth _ _ root) in Hy.
  destruct Hy as [j [Hj Hy]].
  subst y.
  rewrite <-node_at_app.
  apply H1. lia.
Qed.
