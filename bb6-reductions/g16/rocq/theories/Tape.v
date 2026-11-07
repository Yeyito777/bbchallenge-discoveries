(** Tape shapes, walking lemmas, and mirror images without funext. *)
From Coq Require Import List Lia.
From BusyCoq Require Import Individual62.
Import ListNotations.
Open Scope list.

Definition ones (n : nat) (x : side) : side := [1]^^n *> x.

Fixpoint RS (l : list nat) : side :=
  match l with
  | [] => const 0
  | a :: t => 0 >> [1]^^a *> RS t
  end.

(** The zigzag shape: state [f] on the last cell of a run of [r+1] ones, left neighbour [p], marker 00, then [y] ones. *)
Definition cfg (f : Q) (lx : side) (p r y : nat) (rx : side) : Q * tape :=
  (f;; [1]^^r *> 0 >> [1]^^p *> lx {{1}} 0 >> 0 >> [1]^^y *> rx).

(** Head on the blank left of the first run. *)
Definition LSc (f : Q) (P : nat) (rx : side) : Q * tape :=
  (f;; const 0 {{0}} [1]^^P *> 0 >> 0 >> 1 >> rx).

(** The right edge: state [a] on the blank past a tape ending in runs 6, 4, c. *)
Definition Cc (a : Q) (c : nat) (s : list nat) : Q * tape :=
  ([1]^^c *> 0 >> [1]^^4 *> 0 >> [1]^^6 *> RS s) {{a}}> const 0.

Definition AP (a : Q) (cur : nat) (lx rx : side) : Q * tape :=
  ([1]^^cur *> lx) {{a}}> rx.

Section Walk.
Variable tm : TM.

Lemma WR q : tm (q, 1) = Some (1, R, q) ->
  forall n l r, l {{q}}> [1]^^n *> r -[ tm ]->* ([1]^^n *> l) {{q}}> r.
Proof.
  intros H n. induction n; intros l r.
  - simpl. apply evstep_refl.
  - cbn [lpow app Str_app]. simpl.
    eapply evstep_step.
    + eapply step_right. exact H.
    + eapply evstep_trans.
      * apply (IHn (1 >> l) r).
      * replace ([1]^^n *> 1 >> l) with (1 >> [1]^^n *> l) by (symmetry; rewrite <- lpow_shift1; reflexivity).
        apply evstep_refl.
Qed.

Lemma WL q : tm (q, 1) = Some (1, L, q) ->
  forall n l r, ([1]^^n *> l) <{{q}} r -[ tm ]->* l <{{q}} [1]^^n *> r.
Proof.
  intros H n. induction n; intros l r.
  - simpl. apply evstep_refl.
  - cbn [lpow app Str_app]. simpl.
    eapply evstep_step.
    + eapply step_left. exact H.
    + eapply evstep_trans.
      * apply (IHn l (1 >> r)).
      * replace ([1]^^n *> 1 >> r) with (1 >> [1]^^n *> r) by (symmetry; rewrite <- lpow_shift1; reflexivity).
        apply evstep_refl.
Qed.
End Walk.

(** Normal form of tapes. *)
Lemma n1a (x : Stream Sym) k : [1]^^k *> 1 >> x = [1]^^(S k) *> x.
Proof. rewrite lpow_shift1. reflexivity. Qed.
Lemma n1b (x : Stream Sym) k : 1 >> [1]^^k *> x = [1]^^(S k) *> x.
Proof. reflexivity. Qed.
Lemma padd (x : Stream Sym) a b : [1]^^a *> [1]^^b *> x = [1]^^(a + b) *> x.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma appcons (a : Sym) (w : list Sym) (x : Stream Sym) : (a :: w) *> x = a >> w *> x.
Proof. reflexivity. Qed.
Lemma appnil (x : Stream Sym) : [] *> x = x.
Proof. reflexivity. Qed.
Lemma p0nil (x : Stream Sym) : [1]^^0 *> x = x.
Proof. reflexivity. Qed.
Lemma n1c (x : Stream Sym) k : [1]^^k *> 1 >> x = 1 >> [1]^^k *> x.
Proof. rewrite n1a, n1b. reflexivity. Qed.
Ltac nz := repeat rewrite n1c.

Create HintDb g16n.
#[export] Hint Rewrite n1a n1b padd appcons appnil p0nil : g16n.

Ltac teq := solve [reflexivity | (autorewrite with g16n; repeat (reflexivity || lia || f_equal))].
Ltac cfin := apply evstep_refl'; teq.

(** Mirror images, no axioms. *)
Definition swapd (d : dir) : dir := match d with L => R | R => L end.
Definition mirror (tm : TM) : TM := fun qs =>
  match tm qs with
  | Some (s, d, q) => Some (s, swapd d, q)
  | None => None
  end.
Definition mirror_conf (c : Q * tape) : Q * tape :=
  match c with (q, (l, s, r)) => (q, (r, s, l)) end.

Lemma mirror_step tm c c' : c -[ tm ]-> c' -> mirror_conf c -[ mirror tm ]-> mirror_conf c'.
Proof.
  intros H. destruct H as [q q' s s' l r E | q q' s s' l r E].
  - eapply step_right. unfold mirror. rewrite E. reflexivity.
  - eapply step_left. unfold mirror. rewrite E. reflexivity.
Qed.

Lemma unmirror_step tm c c' : c -[ mirror tm ]-> c' -> mirror_conf c -[ tm ]-> mirror_conf c'.
Proof.
  intros H. destruct H as [q q' s s' l r E | q q' s s' l r E];
  unfold mirror in E; destruct (tm (q, s)) as [[[x d] y]|] eqn:T; try discriminate;
  injection E as <- Hd <-; destruct d; try discriminate.
  - eapply step_right. exact T.
  - eapply step_left. exact T.
Qed.

Lemma mirror_ms tm n c c' : c -[ tm ]->> n / c' -> mirror_conf c -[ mirror tm ]->> n / mirror_conf c'.
Proof. intros H. induction H; econstructor; eauto using mirror_step. Qed.
Lemma unmirror_ms tm n c c' : c -[ mirror tm ]->> n / c' -> mirror_conf c -[ tm ]->> n / mirror_conf c'.
Proof. intros H. induction H; econstructor; eauto using unmirror_step. Qed.

Lemma mirror_c0 : mirror_conf c0 = c0.
Proof. reflexivity. Qed.

Lemma mirror_halts tm : halts tm c0 <-> halts (mirror tm) c0.
Proof.
  split; intros [n [ch [H1 H2]]]; exists n.
  - exists (mirror_conf ch). split.
    + rewrite <- mirror_c0. apply mirror_ms. exact H1.
    + destruct ch as [q [[l s] r]]. simpl in *. unfold mirror. rewrite H2. reflexivity.
  - exists (mirror_conf ch). split.
    + rewrite <- mirror_c0. apply unmirror_ms. exact H1.
    + destruct ch as [q [[l s] r]]. simpl in *. unfold mirror in H2.
      destruct (tm (q, s)) as [[[x d] y]|]; [discriminate|reflexivity].
Qed.
