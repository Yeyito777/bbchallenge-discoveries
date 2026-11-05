(** Champions: an explicit tiling of the dxd square, checked edge by edge, and the refutation
    search of Wang_Refute.v run with tiles as labels, showing that (d+1)x(d+1) cannot be tiled. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Geom Wang_Upper Wang_Refute.

(** Tiles as labels: label i is the i-th tile of the list. *)
Definition hrelT (T : list tile) (a b : nat) : bool := Nat.eqb (right (nth a T dflt_tile)) (left (nth b T dflt_tile)).
Definition vrelT (T : list tile) (a b : nat) : bool := Nat.eqb (bottom (nth a T dflt_tile)) (top (nth b T dflt_tile)).

Definition refutes (T : list tile) (d : nat) : bool :=
  refute_top (length T) (hrelT T) (vrelT T) d (centre_order d) (4 * (length T + 2) * (d * d)).

Theorem refutes_no_square : forall T d, refutes T d = true -> ~ tiles_square T d.
Proof.
  intros T d E [f [Hin [H1 H2]]].
  set (F := fun r c => tindex (f r c) T).
  apply (refute_top_sound (length T) (hrelT T) (vrelT T) d (centre_order d) _ (centre_order_spec d) E F).
  split; [|split].
  - intros r c Hr Hc. apply tindex_spec. apply Hin; assumption.
  - intros r c Hr Hc. unfold hrelT, F.
    rewrite (proj2 (tindex_spec _ _ (Hin r c Hr ltac:(lia)))), (proj2 (tindex_spec _ _ (Hin r (S c) Hr Hc))).
    apply Nat.eqb_eq. apply H1; assumption.
  - intros r c Hr Hc. unfold vrelT, F.
    rewrite (proj2 (tindex_spec _ _ (Hin r c ltac:(lia) Hc))), (proj2 (tindex_spec _ _ (Hin (S r) c Hr Hc))).
    apply Nat.eqb_eq. apply H2; assumption.
Qed.

(** ** Explicit tilings *)

Definition check_tiling (T : list tile) (d : nat) (G : list (list nat)) : bool :=
  forallb (fun r => forallb (fun c =>
     let x := nth c (nth r G []) 0 in
     Nat.ltb x (length T) &&
     (implb (Nat.ltb (S c) d) (hrelT T x (nth (S c) (nth r G []) 0))) &&
     (implb (Nat.ltb (S r) d) (vrelT T x (nth c (nth (S r) G []) 0)))) (seq 0 d)) (seq 0 d).

Theorem check_tiling_square : forall T d G, check_tiling T d G = true -> tiles_square T d.
Proof.
  intros T d G E. exists (fun r c => nth (nth c (nth r G []) 0) T dflt_tile).
  unfold check_tiling in E. rewrite forallb_forall in E.
  assert (A : forall r c, r < d -> c < d ->
    Nat.ltb (nth c (nth r G []) 0) (length T) = true /\
    implb (Nat.ltb (S c) d) (hrelT T (nth c (nth r G []) 0) (nth (S c) (nth r G []) 0)) = true /\
    implb (Nat.ltb (S r) d) (vrelT T (nth c (nth r G []) 0) (nth c (nth (S r) G []) 0)) = true).
  { intros r c Hr Hc. specialize (E r ltac:(apply in_seq; lia)). rewrite forallb_forall in E.
    specialize (E c ltac:(apply in_seq; lia)). repeat rewrite andb_true_iff in E. tauto. }
  split; [|split].
  - intros r c Hr Hc. apply nth_In. apply Nat.ltb_lt. apply (A r c Hr Hc).
  - intros r c Hr Hc. destruct (A r c Hr ltac:(lia)) as [_ [B _]].
    rewrite (proj2 (Nat.ltb_lt _ _) Hc) in B. simpl in B. unfold hrelT in B. apply Nat.eqb_eq. exact B.
  - intros r c Hr Hc. destruct (A r c ltac:(lia) Hc) as [_ [_ B]].
    rewrite (proj2 (Nat.ltb_lt _ _) Hr) in B. simpl in B. unfold vrelT in B. apply Nat.eqb_eq. exact B.
Qed.

(** A champion: tiles dxd and refuses (d+1)x(d+1), so its score is d. *)
Theorem champion_score : forall T d G, check_tiling T d G = true -> refutes T (S d) = true -> score T d.
Proof.
  intros T d G E1 E2. left. split; [apply (check_tiling_square T d G E1)|].
  intros e He. destruct (Nat.le_gt_cases e d) as [H|H]; [exact H|]. exfalso.
  apply (refutes_no_square T (S d) E2). apply (tiles_square_le T (S d) e); [lia|exact He].
Qed.
