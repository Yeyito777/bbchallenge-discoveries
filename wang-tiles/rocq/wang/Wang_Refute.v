(** A search proving that no dxd square can be labelled with labels 0..n-1 so that horizontal
    neighbours are related by [hrel] and vertical ones by [vrel]. It keeps a set of possible labels
    per cell, removes labels that no neighbour allows (arc consistency), and branches on one cell,
    centre first. Used for the champions (labels are tiles) and for the closed claims of the
    certificate checker (labels are related by the colour equalities known so far).
    *)
From Coq Require Import List Arith Lia Bool PArith FMapPositive.
Import ListNotations.
From WangTiles Require Import Wang_Rel.
Module PM := PositiveMap.

Lemma nth_map_seq_gen : forall {A} (f : nat -> A) p m (dflt : A), p < m -> nth p (map f (seq 0 m)) dflt = f p.
Proof.
  intros A f p m dflt Hp. rewrite nth_indep with (d' := f 0) by (rewrite length_map, length_seq; exact Hp).
  rewrite map_nth, seq_nth by exact Hp. reflexivity.
Qed.

Section Refute.
Variable n : nat.
Variables hrel vrel : nat -> nat -> bool.

Definition dom := list bool.
Definition dmem (m : dom) (t : nat) : bool := nth t m false.

Fixpoint andl (x y : list bool) : list bool :=
  match x, y with a :: x', b :: y' => (a && b) :: andl x' y' | _, _ => [] end.

Lemma dmem_andl : forall x y t, dmem (andl x y) t = dmem x t && dmem y t.
Proof.
  unfold dmem. induction x as [|a x IH]; intros [|b y] [|t]; simpl; auto; try (destruct a; reflexivity).
  destruct (nth t x false); reflexivity.
Qed.

Definition full : dom := repeat true n.

Lemma dmem_full : forall t, t < n -> dmem full t = true.
Proof. intros t Ht. unfold dmem, full. apply nth_repeat_lt. exact Ht. Qed.

Variable d : nat.

(** Cells (r, c) are keyed by the positive [kk r c]; a missing key means "any label". *)
Definition kk (r c : nat) : positive := Pos.of_succ_nat (r * d + c).
Definition getd (m : PM.t dom) (p : positive) : dom := match PM.find p m with Some v => v | None => full end.

Definition reldir (dir t u : nat) : bool :=
  match dir with 0 => hrel t u | 1 => hrel u t | 2 => vrel t u | _ => vrel u t end.

(** The neighbours of (r, c): right, left, below, above, each with its direction. *)
Definition nbs (r c : nat) : list (positive * nat) :=
  (if Nat.ltb (S c) d then [(kk r (S c), 0)] else []) ++
  (if Nat.ltb 0 c then [(kk r (c - 1), 1)] else []) ++
  (if Nat.ltb (S r) d then [(kk (S r) c, 2)] else []) ++
  (if Nat.ltb 0 r then [(kk (r - 1) c, 3)] else []).

Definition cells : list (nat * nat) := flat_map (fun r => map (fun c => (r, c)) (seq 0 d)) (seq 0 d).

Definition mk_tbl : PM.t (nat * nat * list (positive * nat)) :=
  fold_left (fun m x => PM.add (kk (fst x) (snd x)) (fst x, snd x, nbs (fst x) (snd x)) m) cells (PM.empty _).

(** u can be at a neighbour in direction dir of a cell holding some label of m. *)
Definition rows (dir : nat) : list (list bool) := map (fun t => map (fun u => reldir dir t u) (seq 0 n)) (seq 0 n).

Definition img (rw : list (list bool)) (m : dom) : dom :=
  fold_left (fun acc t => if dmem m t then orl acc (nth t rw []) else acc) (seq 0 n) (repeat false n).

Record ctx := mkC { c_tbl : PM.t (nat * nat * list (positive * nat)); c_rows : list (list (list bool)) }.
Definition mk_ctx : ctx := mkC mk_tbl (map rows [0; 1; 2; 3]).

Fixpoint dom_eqb (x y : dom) : bool :=
  match x, y with [] , [] => true | a :: x', b :: y' => Bool.eqb a b && dom_eqb x' y' | _, _ => false end.

Definition is_empty (m : dom) : bool := negb (existsb (fun t => dmem m t) (seq 0 n)).

(** Revise the neighbours of the cell keyed p; None means a domain became empty. *)
Fixpoint revise (cx : ctx) (m : PM.t dom) (dp : dom) (l : list (positive * nat)) (wl : list positive)
  : option (PM.t dom * list positive) :=
  match l with
  | [] => Some (m, wl)
  | (q, dir) :: l' =>
    let dq := getd m q in
    let nw := andl dq (img (nth dir (c_rows cx) []) dp) in
    if dom_eqb nw dq then revise cx m dp l' wl
    else if is_empty nw then None
    else revise cx (PM.add q nw m) dp l' (q :: wl)
  end.

Fixpoint propagate (cx : ctx) (fuel : nat) (m : PM.t dom) (wl : list positive) : option (PM.t dom) :=
  match fuel with
  | O => Some m
  | S f =>
    match wl with
    | [] => Some m
    | p :: wl' =>
      match PM.find p (c_tbl cx) with
      | None => propagate cx f m wl'
      | Some (_, _, l) =>
        match revise cx m (getd m p) l wl' with
        | None => None
        | Some (m', wl'') => propagate cx f m' wl''
        end
      end
    end
  end.

Fixpoint count (m : dom) : nat := match m with [] => 0 | b :: m' => (if b then 1 else 0) + count m' end.

Fixpoint choose (m : PM.t dom) (order : list (nat * nat * positive)) : option (nat * nat * positive) :=
  match order with
  | [] => None
  | x :: o => if Nat.ltb 1 (count (getd m (snd x))) then Some x else choose m o
  end.

Definition single (t : nat) : dom := map (fun u => Nat.eqb u t) (seq 0 n).

Variable order : list (nat * nat * positive).
Variable pfuel : nat.

Fixpoint refute (cx : ctx) (fuel : nat) (m : PM.t dom) : bool :=
  match fuel with
  | O => false
  | S f =>
    match choose m order with
    | None => false
    | Some (r, c, p) =>
      forallb (fun t => implb (dmem (getd m p) t)
        (match propagate cx pfuel (PM.add p (single t) m) [p] with
         | None => true
         | Some m' => refute cx f m'
         end)) (seq 0 n)
    end
  end.

(** [tbl] is [mk_tbl], passed in so that a caller can compute it once. *)
Definition refute_top_t (tbl : PM.t (nat * nat * list (positive * nat))) : bool :=
  let cx := mkC tbl (map rows [0; 1; 2; 3]) in
  match propagate cx pfuel (PM.empty _) (map (fun x => kk (fst x) (snd x)) cells) with
  | None => true
  | Some m => refute cx (S (d * d)) m
  end.

Definition refute_top : bool := refute_top_t mk_tbl.

(** ** Soundness *)

Definition ltiling (F : nat -> nat -> nat) : Prop :=
  (forall r c, r < d -> c < d -> F r c < n) /\
  (forall r c, r < d -> S c < d -> hrel (F r c) (F r (S c)) = true) /\
  (forall r c, S r < d -> c < d -> vrel (F r c) (F (S r) c) = true).

Definition consistent (m : PM.t dom) (F : nat -> nat -> nat) : Prop :=
  forall r c, r < d -> c < d -> dmem (getd m (kk r c)) (F r c) = true.

Lemma kk_inj : forall r1 c1 r2 c2, c1 < d -> c2 < d -> kk r1 c1 = kk r2 c2 -> r1 = r2 /\ c1 = c2.
Proof.
  intros r1 c1 r2 c2 H1 H2 E. unfold kk in E. apply SuccNat2Pos.inj in E.
  destruct (Nat.lt_trichotomy r1 r2) as [Hr|[Hr|Hr]].
  - exfalso. assert (r1 * d + d <= r2 * d) by nia. lia.
  - subst. split; [reflexivity|lia].
  - exfalso. assert (r2 * d + d <= r1 * d) by nia. lia.
Qed.

Lemma nth_map_seq_b : forall (f : nat -> list bool) p m, p < m -> nth p (map f (seq 0 m)) [] = f p.
Proof. intros. apply nth_map_seq_gen. assumption. Qed.

Lemma dmem_img : forall dir m t u, t < n -> u < n -> dmem m t = true -> reldir dir t u = true ->
  dmem (img (rows dir) m) u = true.
Proof.
  intros dir m t u Ht Hu Hm Hr. unfold img.
  assert (G : forall l acc, (In t l -> True) -> (dmem acc u = true \/ In t l) ->
    dmem (fold_left (fun acc t => if dmem m t then orl acc (nth t (rows dir) []) else acc) l acc) u = true).
  { induction l as [|t' l IH]; intros acc _ [Ha|Hl]; simpl; [exact Ha|destruct Hl|apply IH; auto|].
    - left. destruct (dmem m t'); [|exact Ha]. unfold dmem in *. rewrite nth_orl, Ha. reflexivity.
    - destruct Hl as [<-|Hl]; [|apply IH; auto].
      apply IH; [auto|]. left. rewrite Hm. unfold dmem. rewrite nth_orl.
      unfold rows. rewrite nth_map_seq_b by exact Ht. rewrite nth_map_seq_gen by exact Hu. rewrite Hr. apply orb_true_r. }
  apply G; [auto|]. right. apply in_seq. lia.
Qed.

Lemma nbs_spec : forall r c q dir, r < d -> c < d -> In (q, dir) (nbs r c) ->
  exists r' c', r' < d /\ c' < d /\ q = kk r' c' /\
    forall F, ltiling F -> reldir dir (F r c) (F r' c') = true.
Proof.
  intros r c q dir Hr Hc Hin. unfold nbs in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]]].
  - destruct (Nat.ltb_spec (S c) d); simpl in Hin; [|contradiction]. destruct Hin as [E|[]]. inversion E; subst.
    exists r, (S c). split; [lia|]. split; [lia|]. split; [reflexivity|]. intros F [_ [Hh _]]. apply Hh; lia.
  - destruct (Nat.ltb_spec 0 c); simpl in Hin; [|contradiction]. destruct Hin as [E|[]]. inversion E; subst.
    exists r, (c - 1). split; [lia|]. split; [lia|]. split; [reflexivity|]. intros F [_ [Hh _]]. simpl.
    pose proof (Hh r (c - 1) Hr ltac:(lia)) as X. replace (S (c - 1)) with c in X by lia. exact X.
  - destruct (Nat.ltb_spec (S r) d); simpl in Hin; [|contradiction]. destruct Hin as [E|[]]. inversion E; subst.
    exists (S r), c. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros F [_ [_ Hv]]. apply Hv; lia.
  - destruct (Nat.ltb_spec 0 r); simpl in Hin; [|contradiction]. destruct Hin as [E|[]]. inversion E; subst.
    exists (r - 1), c. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros F [_ [_ Hv]]. simpl.
    pose proof (Hv (r - 1) c ltac:(lia) Hc) as X. replace (S (r - 1)) with r in X by lia. exact X.
Qed.

Lemma tbl_spec : forall p r c l, PM.find p mk_tbl = Some (r, c, l) -> r < d /\ c < d /\ p = kk r c /\ l = nbs r c.
Proof.
  intros p r c l. unfold mk_tbl.
  assert (G : forall xs m0, (forall p r c l, PM.find p m0 = Some (r, c, l) -> r < d /\ c < d /\ p = kk r c /\ l = nbs r c) ->
    (forall x, In x xs -> fst x < d /\ snd x < d) ->
    PM.find p (fold_left (fun m x => PM.add (kk (fst x) (snd x)) (fst x, snd x, nbs (fst x) (snd x)) m) xs m0) = Some (r, c, l) ->
    r < d /\ c < d /\ p = kk r c /\ l = nbs r c).
  { induction xs as [|x xs IH]; intros m0 H0 Hxs E; simpl in E; [apply (H0 _ _ _ _ E)|].
    apply (IH (PM.add (kk (fst x) (snd x)) (fst x, snd x, nbs (fst x) (snd x)) m0)); [|intros; apply Hxs; right; assumption|exact E].
    intros p' r' c' l' E'. destruct (Pos.eq_dec p' (kk (fst x) (snd x))) as [->|Hne].
    - rewrite PM.gss in E'. inversion E'; subst. destruct (Hxs x (or_introl eq_refl)). auto.
    - rewrite PM.gso in E' by exact Hne. apply (H0 _ _ _ _ E'). }
  apply G.
  - intros p' r' c' l' E'. rewrite PM.gempty in E'. discriminate.
  - intros x Hx. unfold cells in Hx. apply in_flat_map in Hx as [r0 [Hr0 Hx]]. apply in_map_iff in Hx as [c0 [<- Hc0]].
    apply in_seq in Hr0, Hc0. simpl. lia.
Qed.

Lemma getd_add : forall m p v q, getd (PM.add p v m) q = if Pos.eqb q p then v else getd m q.
Proof.
  intros m p v q. unfold getd. destruct (Pos.eqb_spec q p) as [->|Hne].
  - rewrite PM.gss. reflexivity.
  - rewrite PM.gso by exact Hne. reflexivity.
Qed.

Lemma revise_sound : forall cx F, c_rows cx = map rows [0; 1; 2; 3] -> ltiling F ->
  forall l m dp wl r c, r < d -> c < d -> consistent m F -> dmem dp (F r c) = true ->
  (forall q dir, In (q, dir) l -> In (q, dir) (nbs r c)) ->
  match revise cx m dp l wl with None => False | Some (m', _) => consistent m' F end.
Proof.
  intros cx F Hcx HF. induction l as [|[q dir] l IH]; intros m dp wl r c Hr Hc Hm Hdp Hl; simpl; [exact Hm|].
  destruct (nbs_spec r c q dir Hr Hc (Hl q dir (or_introl eq_refl))) as [r' [c' [Hr' [Hc' [-> Hrel]]]]].
  assert (Hdir : dir < 4).
  { pose proof (Hl _ _ (or_introl eq_refl)) as Hn. unfold nbs in Hn.
    repeat (apply in_app_or in Hn; destruct Hn as [Hn|Hn]);
    repeat match type of Hn with context [if ?b then _ else _] => destruct b end;
    simpl in Hn; try contradiction; destruct Hn as [E|[]]; inversion E; lia. }
  assert (Hnw : dmem (andl (getd m (kk r' c')) (img (nth dir (c_rows cx) []) dp)) (F r' c') = true).
  { rewrite dmem_andl, (Hm r' c' Hr' Hc'). simpl. rewrite Hcx.
    replace (nth dir (map rows [0; 1; 2; 3]) []) with (rows dir)
      by (destruct dir as [|[|[|[|]]]]; try reflexivity; lia).
    pose proof (proj1 HF) as HF1. apply (dmem_img dir dp (F r c)); [apply HF1; assumption|apply HF1; assumption|exact Hdp|].
    apply Hrel. exact HF. }
  destruct (dom_eqb _ _).
  - apply (IH m dp wl r c Hr Hc Hm Hdp). intros q0 dir0 H0. apply Hl. right. exact H0.
  - destruct (is_empty _) eqn:Ee.
    + unfold is_empty in Ee. apply negb_true_iff in Ee. rewrite <- not_true_iff_false in Ee. apply Ee.
      apply existsb_exists. exists (F r' c'). split; [apply in_seq; pose proof (proj1 HF r' c' Hr' Hc'); lia|exact Hnw].
    + apply (IH _ dp _ r c Hr Hc); [| exact Hdp |].
      * intros r2 c2 Hr2 Hc2. rewrite getd_add. destruct (Pos.eqb_spec (kk r2 c2) (kk r' c')) as [E|E].
        -- destruct (kk_inj _ _ _ _ Hc2 Hc' E) as [-> ->]. exact Hnw.
        -- apply Hm; assumption.
      * intros q0 dir0 H0. apply Hl. right. exact H0.
Qed.

Lemma propagate_sound : forall F, ltiling F -> forall fuel m wl,
  consistent m F -> match propagate mk_ctx fuel m wl with None => False | Some m' => consistent m' F end.
Proof.
  intros F HF. induction fuel as [|fuel IH]; intros m wl Hm; simpl; [exact Hm|].
  destruct wl as [|p wl']; [exact Hm|].
  destruct (PM.find p mk_tbl) as [[[r c] l]|] eqn:Et; [|apply IH; exact Hm].
  destruct (tbl_spec p r c l Et) as [Hr [Hc [-> ->]]].
  pose proof (revise_sound mk_ctx F eq_refl HF (nbs r c) m (getd m (kk r c)) wl' r c Hr Hc Hm (Hm r c Hr Hc) (fun q dir H => H)) as Hrv.
  destruct (revise mk_ctx m (getd m (kk r c)) (nbs r c) wl') as [[m' wl'']|]; [|exact Hrv].
  apply IH. exact Hrv.
Qed.

Lemma choose_spec : forall m o r c p, (forall x, In x o -> fst (fst x) < d /\ snd (fst x) < d /\ snd x = kk (fst (fst x)) (snd (fst x))) ->
  choose m o = Some (r, c, p) -> r < d /\ c < d /\ p = kk r c.
Proof.
  intros m. induction o as [|x o IH]; intros r c p Ho E; simpl in E; [discriminate|].
  destruct (Nat.ltb 1 (count (getd m (snd x)))).
  - inversion E; subst. apply (Ho _ (or_introl eq_refl)).
  - apply IH; [intros; apply Ho; right; assumption|exact E].
Qed.

Lemma dmem_single : forall t, t < n -> dmem (single t) t = true.
Proof. intros t Ht. unfold dmem, single. rewrite nth_map_seq_gen by exact Ht. apply Nat.eqb_refl. Qed.

Hypothesis Horder : forall x, In x order -> fst (fst x) < d /\ snd (fst x) < d /\ snd x = kk (fst (fst x)) (snd (fst x)).

Lemma refute_sound : forall fuel m F, refute mk_ctx fuel m = true -> ltiling F -> consistent m F -> False.
Proof.
  induction fuel as [|fuel IH]; intros m F E HF Hm; simpl in E; [discriminate|].
  destruct (choose m order) as [[[r c] p]|] eqn:Ech; [|discriminate].
  destruct (choose_spec m order r c p Horder Ech) as [Hr [Hc ->]].
  rewrite forallb_forall in E. pose proof (proj1 HF r c Hr Hc) as Hlt.
  specialize (E (F r c) ltac:(apply in_seq; lia)).
  rewrite (Hm r c Hr Hc) in E. simpl in E.
  assert (Hm' : consistent (PM.add (kk r c) (single (F r c)) m) F).
  { intros r2 c2 Hr2 Hc2. rewrite getd_add. destruct (Pos.eqb_spec (kk r2 c2) (kk r c)) as [E2|E2].
    - destruct (kk_inj _ _ _ _ Hc2 Hc E2) as [-> ->]. apply dmem_single. exact Hlt.
    - apply Hm; assumption. }
  pose proof (propagate_sound F HF pfuel _ [kk r c] Hm') as Hp.
  destruct (propagate mk_ctx pfuel (PM.add (kk r c) (single (F r c)) m) [kk r c]) as [m'|]; [|exact Hp].
  apply (IH m' F E HF Hp).
Qed.

Theorem refute_top_sound : refute_top = true -> forall F, ltiling F -> False.
Proof.
  intros E F HF.
  assert (H0 : consistent (PM.empty _) F).
  { intros r c Hr Hc. unfold getd. rewrite PM.gempty. apply dmem_full. apply HF; assumption. }
  unfold refute_top, refute_top_t in E. fold mk_ctx in E.
  pose proof (propagate_sound F HF pfuel _ (map (fun x => kk (fst x) (snd x)) cells) H0) as Hp.
  destruct (propagate mk_ctx pfuel (PM.empty _) _) as [m|]; [|exact Hp].
  apply (refute_sound _ m F E HF Hp).
Qed.

End Refute.

(** The branching order: cells by distance from the centre, then by position. *)
Fixpoint insert_by (key : nat * nat -> nat) (x : nat * nat) (l : list (nat * nat)) : list (nat * nat) :=
  match l with [] => [x] | y :: l' => if Nat.leb (key x) (key y) then x :: l else y :: insert_by key x l' end.

Lemma in_insert_by : forall key x l y, In y (insert_by key x l) -> y = x \/ In y l.
Proof.
  intros key x. induction l as [|z l IH]; intros y H; simpl in H.
  - destruct H as [<-|[]]. left. reflexivity.
  - destruct (Nat.leb (key x) (key z)); simpl in H.
    + destruct H as [<-|H]; [left; reflexivity|right; exact H].
    + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH y H); [left|right; right]; assumption.
Qed.

Definition centre_key (d : nat) (x : nat * nat) : nat :=
  let '(r, c) := x in
  ((if Nat.leb (2 * r) (d - 1) then d - 1 - 2 * r else 2 * r - (d - 1)) +
   (if Nat.leb (2 * c) (d - 1) then d - 1 - 2 * c else 2 * c - (d - 1))) * (d * d) + (r * d + c).

Definition centre_order (d : nat) : list (nat * nat * positive) :=
  map (fun x => (x, kk d (fst x) (snd x))) (fold_right (insert_by (centre_key d)) [] (cells d)).

Lemma centre_order_spec : forall d x, In x (centre_order d) ->
  fst (fst x) < d /\ snd (fst x) < d /\ snd x = kk d (fst (fst x)) (snd (fst x)).
Proof.
  intros d x Hx. unfold centre_order in Hx. apply in_map_iff in Hx as [y [<- Hy]]. simpl.
  assert (G : forall l z, In z (fold_right (insert_by (centre_key d)) [] l) -> In z l).
  { induction l as [|w l IH]; intros z Hz; simpl in *; [exact Hz|].
    destruct (in_insert_by _ _ _ _ Hz) as [->|H]; [left; reflexivity|right; apply IH; exact H]. }
  apply G in Hy. unfold cells in Hy. apply in_flat_map in Hy as [r [Hr Hy]]. apply in_map_iff in Hy as [c [<- Hc]].
  apply in_seq in Hr, Hc. simpl. repeat split; lia.
Qed.

