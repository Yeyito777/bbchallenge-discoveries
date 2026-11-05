(** Labels named by first appearance, renamings, and the lexicographic order on labellings. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import Wang_Checker.

(** ** Canonical labellings: each label is an old one or the next new one *)

Definition cstep (m x : nat) : nat := if Nat.eqb x m then S m else m.

Fixpoint canon (m : nat) (l : list nat) : Prop :=
  match l with [] => True | x :: l' => x <= m /\ canon (cstep m x) l' end.

Fixpoint cnext (m : nat) (l : list nat) : nat :=
  match l with [] => m | x :: l' => cnext (cstep m x) l' end.

Lemma canon_app : forall l1 l2 m, canon m (l1 ++ l2) <-> canon m l1 /\ canon (cnext m l1) l2.
Proof. induction l1 as [|x l1 IH]; intros l2 m; simpl; [tauto|]. rewrite IH. tauto. Qed.

Lemma cnext_app : forall l1 l2 m, cnext m (l1 ++ l2) = cnext (cnext m l1) l2.
Proof. induction l1 as [|x l1 IH]; intros l2 m; simpl; auto. Qed.

(** A renaming that maps labels below k into labels below k and fixes k..n-1 keeps a labelling
    canonical from any m >= k. *)
Lemma canon_map_perm : forall (p : nat -> nat) k n l m,
  (forall x, x < k -> x < n -> p x < k) -> (forall x, k <= x -> x < n -> p x = x) ->
  (forall x, In x l -> x < n) -> k <= m -> canon m l -> canon m (map p l) /\ cnext m (map p l) = cnext m l.
Proof.
  intros p k n. induction l as [|x l IH]; intros m H1 H2 Hl Hkm Hc; simpl in *; [tauto|].
  destruct Hc as [Hx Hc].
  assert (Ex : p x <= m /\ cstep m (p x) = cstep m x).
  { destruct (Nat.lt_ge_cases x k) as [Hxk|Hxk].
    - pose proof (H1 x Hxk (Hl x (or_introl eq_refl))). unfold cstep.
      destruct (Nat.eqb_spec (p x) m), (Nat.eqb_spec x m); lia.
    - rewrite (H2 x Hxk (Hl x (or_introl eq_refl))). auto. }
  destruct Ex as [Ex1 Ex2]. rewrite Ex2.
  assert (k <= cstep m x) by (unfold cstep; destruct (Nat.eqb x m); lia).
  destruct (IH (cstep m x) H1 H2 (fun y Hy => Hl y (or_intror Hy)) H Hc). auto.
Qed.

(** ** Renaming by first appearance, as in the checker's symmetric skip *)

Fixpoint canon_aux (m : nat) (a : list (nat * nat)) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs' => let '(y, m', a') := rn_step x m a in y :: canon_aux m' a' xs'
  end.

Fixpoint cst (m : nat) (a : list (nat * nat)) (xs : list nat) : nat * list (nat * nat) :=
  match xs with
  | [] => (m, a)
  | x :: xs' => let '(_, m', a') := rn_step x m a in cst m' a' xs'
  end.

Lemma canon_aux_app : forall xs ys m a,
  canon_aux m a (xs ++ ys) = canon_aux m a xs ++ canon_aux (fst (cst m a xs)) (snd (cst m a xs)) ys.
Proof.
  induction xs as [|x xs IH]; intros ys m a; simpl; [reflexivity|].
  destruct (rn_step x m a) as [[y m'] a']. rewrite IH. reflexivity.
Qed.

Lemma length_canon_aux : forall xs m a, length (canon_aux m a xs) = length xs.
Proof.
  induction xs as [|x xs IH]; intros m a; simpl; [reflexivity|].
  destruct (rn_step x m a) as [[y m'] a']. simpl. rewrite IH. reflexivity.
Qed.

Definition getv (x : nat) (a : list (nat * nat)) : nat :=
  match assoc_find x a with Some y => y | None => 0 end.

Lemma assoc_find_in : forall x a y, assoc_find x a = Some y -> In (x, y) a.
Proof.
  intros x. induction a as [|[z v] a IH]; intros y E; simpl in *; [discriminate|].
  destruct (Nat.eqb_spec x z); [inversion E; subst; left; reflexivity|right; apply IH; exact E].
Qed.

Lemma assoc_find_none : forall x a, assoc_find x a = None -> ~ In x (map fst a).
Proof.
  intros x. induction a as [|[z v] a IH]; intros E; simpl in *; [tauto|].
  destruct (Nat.eqb_spec x z); [discriminate|]. intros [H|H]; [congruence|]. apply (IH E H).
Qed.

Lemma assoc_find_nodup : forall x y a, NoDup (map fst a) -> In (x, y) a -> assoc_find x a = Some y.
Proof.
  intros x y. induction a as [|[z v] a IH]; intros Hnd Hin; simpl in *; [tauto|].
  inversion Hnd as [|? ? Hz Hnd']; subst.
  destruct Hin as [E|Hin].
  - inversion E; subst. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb_spec x z); [|apply IH; assumption].
    subst. exfalso. apply Hz. apply (in_map fst) in Hin. exact Hin.
Qed.

(** The invariant of the renaming state: unique keys below n, distinct values below m, m keys. *)
Definition CI (n m : nat) (a : list (nat * nat)) : Prop :=
  NoDup (map fst a) /\ (forall x y, In (x, y) a -> x < n /\ y < m) /\ length a = m /\
  (forall x1 x2 y, In (x1, y) a -> In (x2, y) a -> x1 = x2).

Lemma CI_le : forall n m a, CI n m a -> m <= n.
Proof.
  intros n m a [Hnd [Hr [Hl _]]]. rewrite <- Hl. rewrite <- (length_map fst a).
  rewrite <- (length_seq n 0). apply NoDup_incl_length; [exact Hnd|].
  intros x Hx. apply in_map_iff in Hx as [[x' y] [E Hin]]. simpl in E. subst.
  apply in_seq. pose proof (Hr _ _ Hin). lia.
Qed.

Lemma CI_add : forall n m a x, CI n m a -> assoc_find x a = None -> x < n -> CI n (S m) ((x, m) :: a).
Proof.
  intros n m a x [Hnd [Hr [Hl Hinj]]] E Hx. split; [|split; [|split]].
  - simpl. constructor; [apply assoc_find_none; exact E|exact Hnd].
  - intros x' y' [Ee|Hin].
    + inversion Ee; subst. split; lia.
    + destruct (Hr _ _ Hin). split; lia.
  - simpl. lia.
  - intros x1 x2 y [E1|E1] [E2|E2].
    + inversion E1; inversion E2; subst; reflexivity.
    + inversion E1; subst. destruct (Hr _ _ E2). lia.
    + inversion E2; subst. destruct (Hr _ _ E1). lia.
    + apply (Hinj _ _ _ E1 E2).
Qed.

Lemma rn_step_spec : forall n x m a, CI n m a -> x < n ->
  let '(y, m', a') := rn_step x m a in
  CI n m' a' /\ assoc_find x a' = Some y /\ y <= m /\ cstep m y = m' /\
  (forall z v, assoc_find z a = Some v -> assoc_find z a' = Some v).
Proof.
  intros n x m a HCI Hx. unfold rn_step. destruct (assoc_find x a) as [y|] eqn:E.
  - pose proof HCI as [Hnd [Hr [Hl Hinj]]].
    pose proof (proj2 (Hr _ _ (assoc_find_in _ _ _ E))).
    split; [exact HCI|]. split; [exact E|]. split; [lia|].
    split; [unfold cstep; destruct (Nat.eqb_spec y m); lia|]. auto.
  - pose proof (CI_add n m a x HCI E Hx) as HC'.
    split; [exact HC'|]. split; [simpl; rewrite Nat.eqb_refl; reflexivity|].
    split; [lia|]. split; [unfold cstep; rewrite Nat.eqb_refl; reflexivity|].
    intros z v Ez. simpl. destruct (Nat.eqb_spec z x); [subst; congruence|exact Ez].
Qed.

Lemma canon_aux_spec : forall n xs m a, CI n m a -> (forall x, In x xs -> x < n) ->
  let '(m', a') := cst m a xs in
  CI n m' a' /\ (forall z v, assoc_find z a = Some v -> assoc_find z a' = Some v) /\
  (forall x, In x xs -> assoc_find x a' <> None) /\
  canon_aux m a xs = map (fun x => getv x a') xs /\ canon m (canon_aux m a xs).
Proof.
  intros n. induction xs as [|x xs IH]; intros m a HCI Hxs; simpl.
  - split; [exact HCI|]. split; [auto|]. split; [intros x []|]. split; [reflexivity|exact I].
  - pose proof (rn_step_spec n x m a HCI (Hxs x (or_introl eq_refl))) as Hs.
    destruct (rn_step x m a) as [[y m'] a'] eqn:Er.
    destruct Hs as [HCI' [Hy [Hym [Hc Hmono]]]].
    specialize (IH m' a' HCI' (fun z Hz => Hxs z (or_intror Hz))).
    destruct (cst m' a' xs) as [m'' a''].
    destruct IH as [HCI'' [Hmono' [Hdom [Heq Hcan]]]].
    split; [exact HCI''|]. split; [intros z v Ez; apply Hmono', Hmono, Ez|].
    split; [intros z [Ez|Hz]; [subst z; rewrite (Hmono' _ _ Hy); discriminate|apply Hdom; exact Hz]|].
    split; [rewrite Heq; f_equal; unfold getv; rewrite (Hmono' _ _ Hy); reflexivity|].
    simpl. split; [lia|rewrite Hc; exact Hcan].
Qed.

(** The full statement used in the proofs: renaming by first appearance is an injective map
    into 0..n-1, and its result is canonical. *)
Lemma canon_rename : forall n xs, (forall x, In x xs -> x < n) ->
  exists rho, canon_aux 0 [] xs = map rho xs /\ canon 0 (map rho xs) /\
    (forall x, In x xs -> rho x < n) /\
    (forall x y, In x xs -> In y xs -> rho x = rho y -> x = y).
Proof.
  intros n xs Hxs.
  assert (HCI : CI n 0 []).
  { split; [constructor|]. split; [intros x y []|]. split; [reflexivity|intros x1 x2 y []]. }
  pose proof (canon_aux_spec n xs 0 [] HCI Hxs) as Hs.
  destruct (cst 0 [] xs) as [m' a'] eqn:Ecst.
  destruct Hs as [HCI' [_ [Hdom [Heq Hcan]]]].
  exists (fun x => getv x a'). split; [exact Heq|]. split; [rewrite <- Heq; exact Hcan|]. split.
  - intros x Hx. unfold getv. destruct (assoc_find x a') eqn:E; [|exfalso; apply (Hdom x Hx E)].
    pose proof (CI_le _ _ _ HCI') as Hle. destruct HCI' as [_ [Hr _]].
    pose proof (Hr _ _ (assoc_find_in _ _ _ E)). lia.
  - intros x y Hx Hy E. unfold getv in E.
    destruct (assoc_find x a') eqn:Ex; [|exfalso; apply (Hdom x Hx Ex)].
    destruct (assoc_find y a') eqn:Ey; [|exfalso; apply (Hdom y Hy Ey)].
    subst. destruct HCI' as [_ [_ [_ Hinj]]].
    apply (Hinj _ _ _ (assoc_find_in _ _ _ Ex) (assoc_find_in _ _ _ Ey)).
Qed.

(** A left inverse of an injective renaming on a list. *)
Definition linv (rho : nat -> nat) (xs : list nat) (y : nat) : nat :=
  match find (fun x => Nat.eqb (rho x) y) xs with Some x => x | None => 0 end.

Lemma linv_spec : forall rho xs x, In x xs ->
  (forall x y, In x xs -> In y xs -> rho x = rho y -> x = y) -> linv rho xs (rho x) = x.
Proof.
  intros rho xs x Hx Hinj. unfold linv.
  destruct (find (fun z => Nat.eqb (rho z) (rho x)) xs) as [z|] eqn:E.
  - apply find_some in E as [Hz Ez]. apply Nat.eqb_eq in Ez. apply Hinj; assumption.
  - exfalso. pose proof (find_none _ _ E x Hx). simpl in H. rewrite Nat.eqb_refl in H. discriminate.
Qed.

Lemma linv_lt : forall rho xs n y, 0 < n -> (forall x, In x xs -> x < n) -> linv rho xs y < n.
Proof.
  intros rho xs n y Hn Hxs. unfold linv.
  destruct (find (fun z => Nat.eqb (rho z) y) xs) as [z|] eqn:E; [|exact Hn].
  apply find_some in E as [Hz _]. apply Hxs. exact Hz.
Qed.

(** ** Lexicographic order and the rank of a labelling *)

Definition lexlt (l1 l2 : list nat) : Prop :=
  exists i, i < length l1 /\ firstn i l1 = firstn i l2 /\ nth i l1 0 < nth i l2 0.

Fixpoint rank_from (n acc : nat) (l : list nat) : nat :=
  match l with [] => acc | x :: l' => rank_from n (acc * n + x) l' end.
Definition rank (n : nat) (l : list nat) : nat := rank_from n 0 l.

Lemma rank_from_spec : forall n l acc, rank_from n acc l = acc * n ^ length l + rank_from n 0 l.
Proof.
  intros n. induction l as [|x l IH]; intros acc; simpl; [lia|].
  rewrite (IH (acc * n + x)), (IH x). nia.
Qed.

Lemma rank_from_app : forall n l1 l2 acc, rank_from n acc (l1 ++ l2) = rank_from n (rank_from n acc l1) l2.
Proof. intros n. induction l1 as [|x l1 IH]; intros l2 acc; simpl; [reflexivity|apply IH]. Qed.

Lemma rank_bound : forall n l, (forall x, In x l -> x < n) -> rank n l < n ^ length l.
Proof.
  intros n l. induction l as [|x l IH] using rev_ind; intros Hl; [unfold rank; simpl; lia|].
  unfold rank in *. rewrite length_app. simpl length.
  assert (E : forall acc, rank_from n acc (l ++ [x]) = rank_from n acc l * n + x).
  { clear. induction l as [|y l IH]; intros acc; simpl; [reflexivity|apply IH]. }
  rewrite E. assert (Hx : x < n) by (apply Hl; apply in_or_app; right; left; reflexivity).
  specialize (IH (fun y Hy => Hl y (in_or_app _ _ _ (or_introl Hy)))).
  rewrite Nat.pow_add_r. simpl. nia.
Qed.

Lemma rank_lexlt : forall n l1 l2, length l1 = length l2 ->
  (forall x, In x l1 -> x < n) -> (forall x, In x l2 -> x < n) -> lexlt l1 l2 -> rank n l1 < rank n l2.
Proof.
  intros n l1 l2 Hlen H1 H2 [i [Hi [Hpre Hlt]]].
  rewrite <- (firstn_skipn i l1), <- (firstn_skipn i l2).
  destruct (skipn i l1) as [|x s1] eqn:E1.
  { exfalso. pose proof (length_skipn i l1). rewrite E1 in H. simpl in H. lia. }
  destruct (skipn i l2) as [|y s2] eqn:E2.
  { exfalso. pose proof (length_skipn i l2). rewrite E2 in H. simpl in H. lia. }
  assert (Hx : nth i l1 0 = x).
  { rewrite <- (firstn_skipn i l1), E1, app_nth2; rewrite length_firstn; [|lia].
    replace (i - Nat.min i (length l1)) with 0 by lia. reflexivity. }
  assert (Hy : nth i l2 0 = y).
  { rewrite <- (firstn_skipn i l2), E2, app_nth2; rewrite length_firstn; [|lia].
    replace (i - Nat.min i (length l2)) with 0 by lia. reflexivity. }
  assert (Hs : length s1 = length s2).
  { pose proof (length_skipn i l1). pose proof (length_skipn i l2). rewrite E1 in H. rewrite E2 in H0.
    simpl in *. lia. }
  rewrite Hpre. unfold rank.
  assert (E : forall p z s, rank_from n 0 (p ++ z :: s) = (rank_from n 0 p * n + z) * n ^ length s + rank_from n 0 s).
  { intros p z s. rewrite rank_from_app. simpl. apply rank_from_spec. }
  rewrite !E. rewrite Hs.
  assert (Hb : rank_from n 0 s1 < n ^ length s2).
  { rewrite <- Hs. apply rank_bound. intros z Hz. apply H1.
    rewrite <- (firstn_skipn i l1), E1. apply in_or_app. right. right. exact Hz. }
  subst x y. nia.
Qed.
