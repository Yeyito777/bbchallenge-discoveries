(** Adjacency relations between tile labels, and colour merges. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement.

(** A relation on labels 0..n-1 as a matrix of booleans: row a, column b. *)
Definition rel := list (list bool).
Definition rget (R : rel) (a b : nat) : bool := nth b (nth a R []) false.
Definition rempty (n : nat) : rel := repeat (repeat false n) n.

(** A labelling of tiles [col] satisfies [R] for the edge pair (fr, fl): every related pair
    (a, b) has fr (col a) = fl (col b). *)
Definition sat (fr fl : tile -> nat) (col : nat -> tile) (R : rel) : Prop :=
  forall a b, rget R a b = true -> fr (col a) = fl (col b).

Fixpoint orl (x y : list bool) : list bool :=
  match x, y with
  | [], _ => y
  | _, [] => x
  | a :: x', b :: y' => (a || b) :: orl x' y'
  end.

Fixpoint inter (x y : list bool) : bool :=
  match x, y with
  | a :: x', b :: y' => (a && b) || inter x' y'
  | _, _ => false
  end.

Definition unit_row (b : nat) : list bool := repeat false b ++ [true].

Fixpoint mapi_from {A B} (f : nat -> A -> B) (i : nat) (l : list A) : list B :=
  match l with [] => [] | x :: l' => f i x :: mapi_from f (S i) l' end.

(** Merge the colour classes of "a's edge" and "b's edge": afterwards a relates to b, and so
    does everything forced by it. Rows in a's class are those sharing a partner with a; rows
    in b's class are those related to b. *)
Definition merge0 (R : rel) (a b : nat) : rel :=
  let ra := nth a R [] in
  let J := orl ra (fold_right (fun r acc => if nth b r false then orl r acc else acc) (unit_row b) R) in
  mapi_from (fun i r => if Nat.eqb i a || inter r ra || nth b r false then orl r J else r) 0 R.

(** Nothing to do when a already relates to b. *)
Definition merge (R : rel) (a b : nat) : rel := if rget R a b then R else merge0 R a b.

Definition rincl (P : list (nat * nat)) (R : rel) : bool :=
  forallb (fun p => rget R (fst p) (snd p)) P.

(** Rename a relation through a permutation given by its inverse [inv]: the result relates
    x to y exactly when R relates (inv x) to (inv y). *)
Definition rrename (n : nat) (inv : list nat) (R : rel) : rel :=
  map (fun x => map (fun y => rget R (nth x inv 0) (nth y inv 0)) (seq 0 n)) (seq 0 n).

Fixpoint list_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => Nat.eqb x y && list_eqb l1' l2'
  | _, _ => false
  end.

Fixpoint bl_eqb (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => Bool.eqb x y && bl_eqb l1' l2'
  | _, _ => false
  end.

Fixpoint rel_eqb (r1 r2 : rel) : bool :=
  match r1, r2 with
  | [], [] => true
  | x :: r1', y :: r2' => bl_eqb x y && rel_eqb r1' r2'
  | _, _ => false
  end.

(** ** Lemmas *)

Lemma nth_orl : forall x y j, nth j (orl x y) false = nth j x false || nth j y false.
Proof.
  induction x as [|a x IH]; intros [|b y] [|j]; simpl; auto; try (rewrite orb_false_r; reflexivity).
Qed.

Lemma inter_spec : forall x y, inter x y = true -> exists j, nth j x false = true /\ nth j y false = true.
Proof.
  induction x as [|a x IH]; intros [|b y]; simpl; try discriminate.
  intros E. apply orb_true_iff in E. destruct E as [E|E].
  - apply andb_true_iff in E. exists 0. simpl. tauto.
  - destruct (IH y E) as [j Hj]. exists (S j). exact Hj.
Qed.

Lemma nth_unit_row : forall b, nth b (unit_row b) false = true.
Proof. intros b. unfold unit_row. rewrite app_nth2; rewrite repeat_length; [|lia]. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma nth_unit_row_other : forall b j, j <> b -> nth j (unit_row b) false = false.
Proof.
  intros b j Hj. unfold unit_row. destruct (Nat.lt_ge_cases j b).
  - rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
    destruct (j - b) eqn:E; [lia|]. simpl. destruct n; reflexivity.
Qed.

Lemma nth_mapi_from : forall {A B} (f : nat -> A -> B) l i j d dB,
  j < length l -> nth j (mapi_from f i l) dB = f (i + j) (nth j l d).
Proof.
  induction l as [|x l IH]; intros i j d dB Hj; simpl in *; [lia|].
  destruct j; [f_equal; lia|]. rewrite (IH (S i) j d dB) by lia. f_equal. lia.
Qed.

Lemma nth_mapi_from_out : forall {A B} (f : nat -> A -> B) l i j dB,
  length l <= j -> nth j (mapi_from f i l) dB = dB.
Proof.
  induction l as [|x l IH]; intros i j dB Hj; simpl in *; [destruct j; reflexivity|].
  destruct j; [lia|]. apply IH. lia.
Qed.

Lemma length_mapi_from : forall {A B} (f : nat -> A -> B) l i, length (mapi_from f i l) = length l.
Proof. induction l; simpl; auto. Qed.

Lemma length_merge0 : forall R a b, length (merge0 R a b) = length R.
Proof. intros. unfold merge0. apply length_mapi_from. Qed.

Lemma length_merge : forall R a b, length (merge R a b) = length R.
Proof. intros. unfold merge. destruct (rget R a b); [reflexivity|apply length_merge0]. Qed.

Definition merge_J (R : rel) (a b : nat) : list bool :=
  orl (nth a R []) (fold_right (fun r acc => if nth b r false then orl r acc else acc) (unit_row b) R).

Definition merge_I (R : rel) (a b i : nat) : bool :=
  Nat.eqb i a || inter (nth i R []) (nth a R []) || nth b (nth i R []) false.

Lemma rget_merge : forall R a b i j,
  rget (merge0 R a b) i j = rget R i j || (Nat.ltb i (length R) && merge_I R a b i && nth j (merge_J R a b) false).
Proof.
  intros R a b i j. unfold rget, merge0.
  destruct (Nat.lt_ge_cases i (length R)) as [Hi|Hi].
  - rewrite (nth_mapi_from _ _ _ _ []) by exact Hi. simpl.
    assert (Nat.ltb i (length R) = true) as -> by (apply Nat.ltb_lt; exact Hi). simpl.
    unfold merge_I, merge_J. destruct (_ || _ || _); simpl.
    + rewrite nth_orl. reflexivity.
    + rewrite orb_false_r. reflexivity.
  - rewrite nth_mapi_from_out by exact Hi. rewrite (nth_overflow R) by exact Hi.
    assert (Nat.ltb i (length R) = false) as -> by (apply Nat.ltb_ge; exact Hi).
    destruct j; reflexivity.
Qed.

Lemma fold_J_spec : forall R b j,
  nth j (fold_right (fun r acc => if nth b r false then orl r acc else acc) (unit_row b) R) false = true ->
  j = b \/ exists i, rget R i b = true /\ rget R i j = true.
Proof.
  induction R as [|r R IH]; intros b j E; simpl in E.
  - destruct (Nat.eq_dec j b); [left; assumption|]. rewrite nth_unit_row_other in E by assumption. discriminate.
  - destruct (nth b r false) eqn:Eb.
    + rewrite nth_orl in E. apply orb_true_iff in E. destruct E as [E|E].
      * right. exists 0. unfold rget. simpl. tauto.
      * destruct (IH b j E) as [H|[i Hi]]; [left; assumption|]. right. exists (S i). exact Hi.
    + destruct (IH b j E) as [H|[i Hi]]; [left; assumption|]. right. exists (S i). exact Hi.
Qed.

Lemma merge_sound : forall fr fl col R a b,
  sat fr fl col R -> fr (col a) = fl (col b) -> sat fr fl col (merge R a b).
Proof.
  intros fr fl col R a b HR Hab. unfold merge. destruct (rget R a b); [exact HR|].
  intros i j E. rewrite rget_merge in E.
  apply orb_true_iff in E. destruct E as [E|E]; [apply HR; exact E|].
  apply andb_true_iff in E as [E HJ]. apply andb_true_iff in E as [_ HI].
  assert (Hi : fr (col i) = fr (col a)).
  { unfold merge_I in HI. apply orb_true_iff in HI as [HI|HI]; [apply orb_true_iff in HI as [HI|HI]|].
    - apply Nat.eqb_eq in HI. subst. reflexivity.
    - destruct (inter_spec _ _ HI) as [j' [H1 H2]].
      rewrite (HR i j' H1). symmetry. apply HR. exact H2.
    - rewrite (HR i b HI). symmetry. exact Hab. }
  assert (Hj : fl (col j) = fr (col a)).
  { unfold merge_J in HJ. rewrite nth_orl in HJ. apply orb_true_iff in HJ as [HJ|HJ].
    - symmetry. apply HR. exact HJ.
    - destruct (fold_J_spec _ _ _ HJ) as [->|[i' [H1 H2]]]; [symmetry; exact Hab|].
      rewrite <- (HR i' j H2). rewrite (HR i' b H1). symmetry. exact Hab. }
  rewrite Hi, Hj. reflexivity.
Qed.

Lemma merge_mono : forall R a b i j, rget R i j = true -> rget (merge R a b) i j = true.
Proof. intros. unfold merge. destruct (rget R a b); [exact H|]. rewrite rget_merge, H. reflexivity. Qed.

Lemma merge_complete : forall R a b, a < length R -> rget (merge R a b) a b = true.
Proof.
  intros R a b Ha. unfold merge. destruct (rget R a b) eqn:E; [exact E|].
  rewrite rget_merge. apply orb_true_iff. right.
  assert (Nat.ltb a (length R) = true) as -> by (apply Nat.ltb_lt; exact Ha).
  unfold merge_I. rewrite Nat.eqb_refl. simpl.
  unfold merge_J. rewrite nth_orl. apply orb_true_iff. right.
  clear Ha E. induction R as [|r R IH]; simpl; [apply nth_unit_row|].
  destruct (nth b r false); [rewrite nth_orl, IH, orb_true_r; reflexivity | exact IH].
Qed.

Lemma rincl_spec : forall P R p, rincl P R = true -> In p P -> rget R (fst p) (snd p) = true.
Proof. intros P R p E Hp. unfold rincl in E. rewrite forallb_forall in E. apply E. exact Hp. Qed.

Lemma rget_rrename : forall n inv R x y, x < n -> y < n ->
  rget (rrename n inv R) x y = rget R (nth x inv 0) (nth y inv 0).
Proof.
  intros n inv R x y Hx Hy. unfold rget, rrename.
  rewrite nth_indep with (d' := map (fun y0 => rget R (nth 0 inv 0) (nth y0 inv 0)) (seq 0 n))
    by (rewrite length_map, length_seq; exact Hx).
  rewrite (map_nth (fun x0 => map (fun y0 => rget R (nth x0 inv 0) (nth y0 inv 0)) (seq 0 n))).
  rewrite seq_nth by exact Hx. simpl.
  rewrite nth_indep with (d' := rget R (nth x inv 0) (nth 0 inv 0)) by (rewrite length_map, length_seq; exact Hy).
  rewrite (map_nth (fun y0 => rget R (nth x inv 0) (nth y0 inv 0))).
  rewrite seq_nth by exact Hy. reflexivity.
Qed.

Lemma list_eqb_eq : forall l1 l2, list_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2]; simpl; try discriminate; auto.
  intros E. apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. subst. f_equal. auto.
Qed.

Lemma bl_eqb_eq : forall l1 l2, bl_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2]; simpl; try discriminate; auto.
  intros E. apply andb_true_iff in E as [E1 E2]. apply eqb_prop in E1. subst. f_equal. auto.
Qed.

Lemma rel_eqb_eq : forall r1 r2, rel_eqb r1 r2 = true -> r1 = r2.
Proof.
  induction r1 as [|x r1 IH]; intros [|y r2]; simpl; try discriminate; auto.
  intros E. apply andb_true_iff in E as [E1 E2]. apply bl_eqb_eq in E1. subst. f_equal. auto.
Qed.

Lemma length_rempty : forall n, length (rempty n) = n.
Proof. intros. apply repeat_length. Qed.

Lemma rget_rempty : forall n a b, rget (rempty n) a b = false.
Proof.
  intros n a b. unfold rget, rempty. destruct (Nat.lt_ge_cases a n).
  - rewrite nth_repeat_lt by assumption. apply nth_repeat.
  - rewrite (nth_overflow (repeat (repeat false n) n)) by (rewrite repeat_length; assumption). destruct b; reflexivity.
Qed.

Lemma sat_rempty : forall fr fl col n, sat fr fl col (rempty n).
Proof. intros fr fl col n a b E. rewrite rget_rempty in E. discriminate. Qed.
