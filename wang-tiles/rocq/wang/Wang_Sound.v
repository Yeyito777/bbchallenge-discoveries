(** Soundness of the certificate checker.

    Claim: if [check c] holds, every set of n tiles that tiles the DxD square tiles the plane.

    Proof idea (the one in check_cert.py, made formal). Take any full labelling L of the square
    (canonical: labels named by first appearance) that is valid for some tile set [col]. By
    strong induction on the rank of L, assume every smaller canonical valid labelling, for any
    tile set, gives a plane tiling. Follow L's path down the checker's tree:
    - a torus leaf: its adjacencies all follow from relations that [col] satisfies, so [col]
      tiles a torus, hence the plane;
    - a symmetric skip: a rotated or reflected image of L, renamed, is a smaller canonical valid
      labelling of the rotated tile set, which tiles the plane iff [col] does;
    - a repeat skip: an earlier node had the same state up to a renaming; gluing the rest of L,
      renamed, onto it gives a smaller canonical valid labelling of a renamed tile set;
    - a complete fill with no torus makes the checker fail.
    Nothing is assumed about the certificate data, the caches or the torus table: every claim
    read from them is checked against the relations, or decoded and compared, where it is used. *)

From Coq Require Import List Arith Lia Bool PArith ZArith Wf_nat.
From Coq Require Import Uint63 FMapPositive.
From Coq Require PArray.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Rel Wang_Refute Wang_Checker Wang_Geom Wang_Canon.

Local Open Scope nat_scope.

(** The kernel need not unfold the cache operations to check the proofs below; telling it to
    unfold them last keeps three Qeds from taking 20 s each. *)
Strategy 1000 [cread cfind probe read_token cset cget].

(** ** Small facts *)

Lemma pk_inj : forall p q, pk p = pk q -> p = q.
Proof. intros p q E. apply SuccNat2Pos.inj. exact E. Qed.

Lemma pk_ltb : forall p q, Pos.ltb (pk p) (pk q) = Nat.ltb p q.
Proof.
  intros p q. destruct (Pos.ltb_spec (pk p) (pk q)), (Nat.ltb_spec p q); auto; exfalso.
  - apply Pos2Nat.inj_lt in H. unfold pk in H. rewrite !SuccNat2Pos.id_succ in H. lia.
  - assert (pk q <= pk p)%positive by exact H. apply Pos2Nat.inj_le in H1. unfold pk in H1.
    rewrite !SuccNat2Pos.id_succ in H1. lia.
Qed.

Lemma pk_succ : forall p, Pos.succ (pk p) = pk (S p).
Proof. reflexivity. Qed.

Lemma nth_firstn_lt : forall (l : list nat) i k, i < k -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  induction l as [|x l IH]; intros i k Hik; destruct k; simpl; try lia; try (destruct i; reflexivity).
  destruct i; [reflexivity|]. apply IH. lia.
Qed.

Lemma firstn_S_nth : forall (l : list nat) k, k < length l -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros k Hk; simpl in *; [lia|].
  destruct k; [reflexivity|]. simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_prefix : forall (l pre : list nat) t p, firstn (S p) l = pre ++ [t] -> length pre = p -> firstn p l = pre.
Proof.
  intros l pre t p E Hp. replace (firstn p l) with (firstn p (firstn (S p) l)) by (rewrite firstn_firstn; f_equal; lia).
  rewrite E, firstn_app, Hp, Nat.sub_diag. simpl. rewrite app_nil_r. apply firstn_all2. lia.
Qed.

Lemma nth_map_seq : forall (f : nat -> nat) p m, p < m -> nth p (map f (seq 0 m)) 0 = f p.
Proof.
  intros f p m Hp. rewrite nth_indep with (d' := f 0) by (rewrite length_map, length_seq; exact Hp).
  rewrite map_nth, seq_nth by exact Hp. reflexivity.
Qed.

Lemma nth_map_lt : forall (f : nat -> nat) (l : list nat) p, p < length l -> nth p (map f l) 0 = f (nth p l 0).
Proof.
  intros f l p Hp. rewrite nth_indep with (d' := f 0) by (rewrite length_map; exact Hp). apply map_nth.
Qed.

Lemma in_skipn_in : forall (l : list nat) k x, In x (skipn k l) -> In x l.
Proof. intros l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.

Lemma map_eq_in : forall {A B} (f g : A -> B) l x, map f l = map g l -> In x l -> f x = g x.
Proof.
  induction l as [|y l IH]; intros x E Hx; simpl in *; [tauto|].
  inversion E. destruct Hx as [<-|Hx]; [assumption|]. apply IH; assumption.
Qed.

Lemma seq_S_cons : forall pos m, pos <= m -> seq pos (S m - pos) = pos :: seq (S pos) (S m - S pos).
Proof. intros pos m H. replace (S m - pos) with (S (S m - S pos)) by lia. reflexivity. Qed.

Lemma perm_ok_spec : forall n k nu inv, perm_ok n k nu inv = true ->
  (forall i, i < n -> nth i nu 0 < n /\ nth (nth i nu 0) inv 0 = i /\ (k <= i -> nth i nu 0 = i)) /\
  (forall x, x < n -> nth x inv 0 < n /\ nth (nth x inv 0) nu 0 = x /\ (k <= x -> nth x inv 0 = x)).
Proof.
  intros n k nu inv E. unfold perm_ok in E. apply andb_true_iff in E as [E1 E2].
  rewrite forallb_forall in E1, E2. split.
  - intros i Hi. specialize (E1 i ltac:(apply in_seq; lia)).
    repeat rewrite andb_true_iff in E1. destruct E1 as [[A1 A2] A3].
    apply Nat.ltb_lt in A1. apply Nat.eqb_eq in A2. repeat split; auto.
    intros Hk. apply Nat.leb_le in Hk. rewrite Hk in A3. apply Nat.eqb_eq. exact A3.
  - intros x Hx. specialize (E2 x ltac:(apply in_seq; lia)).
    repeat rewrite andb_true_iff in E2. destruct E2 as [[A1 A2] A3].
    apply Nat.ltb_lt in A1. apply Nat.eqb_eq in A2. repeat split; auto.
    intros Hk. apply Nat.leb_le in Hk. rewrite Hk in A3. apply Nat.eqb_eq. exact A3.
Qed.

Lemma perm_ok_below : forall n k nu inv, perm_ok n k nu inv = true ->
  (forall i, i < k -> i < n -> nth i nu 0 < k) /\ (forall x, x < k -> x < n -> nth x inv 0 < k).
Proof.
  intros n k nu inv E. destruct (perm_ok_spec n k nu inv E) as [P1 P2]. split.
  - intros i Hik Hin. destruct (P1 i Hin) as [A1 [A2 _]].
    destruct (Nat.lt_ge_cases (nth i nu 0) k) as [H|H]; [exact H|].
    destruct (P2 _ A1) as [_ [_ A3]]. rewrite (A3 H) in A2. lia.
  - intros x Hxk Hxn. destruct (P2 x Hxn) as [A1 [A2 _]].
    destruct (Nat.lt_ge_cases (nth x inv 0) k) as [H|H]; [exact H|].
    destruct (P1 _ A1) as [_ [_ A3]]. rewrite (A3 H) in A2. lia.
Qed.

Lemma rst_eqb_eq : forall x y, rst_eqb x y = true -> x = y.
Proof.
  intros [p1 k1 f1 h1 v1] [p2 k2 f2 h2 v2] E. unfold rst_eqb in E. simpl in E.
  repeat rewrite andb_true_iff in E. destruct E as [[[[E1 E2] E3] E4] E5].
  apply Pos.eqb_eq in E1. apply Nat.eqb_eq in E2. apply list_eqb_eq in E3.
  apply rel_eqb_eq in E4. apply rel_eqb_eq in E5. subst. reflexivity.
Qed.

Lemma rst_of_spec : forall n e k lm H V r, rst_of n e k lm H V = Some r ->
  exists nu inv, perm_ok n k nu inv = true /\
    r = mkR (e_key e) k (map (fun l => nth l nu 0) (map (lab lm) (e_front e))) (rrename n inv H) (rrename n inv V).
Proof.
  intros n e k lm H V r E. unfold rst_of in E.
  destruct (compute_nu n k (map (lab lm) (e_front e)) H V) as [nu inv].
  destruct (perm_ok n k nu inv) eqn:Ep; [|discriminate]. inversion E. exists nu, inv. auto.
Qed.

(** ** Merges along the neighbours of a new cell *)

Lemma fold_merge_mono : forall (f : positive -> nat * nat) l R i j,
  rget R i j = true -> rget (fold_left (fun R q => merge R (fst (f q)) (snd (f q))) l R) i j = true.
Proof.
  induction l as [|q l IH]; intros R i j E; simpl; [exact E|]. apply IH. apply merge_mono. exact E.
Qed.

Lemma fold_merge_in : forall (f : positive -> nat * nat) l R q,
  (forall q, In q l -> fst (f q) < length R) -> In q l ->
  rget (fold_left (fun R q => merge R (fst (f q)) (snd (f q))) l R) (fst (f q)) (snd (f q)) = true.
Proof.
  induction l as [|q' l IH]; intros R q Hl Hq; simpl in *; [tauto|].
  destruct Hq as [<-|Hq].
  - apply fold_merge_mono. apply merge_complete. apply Hl. left. reflexivity.
  - apply IH; [|exact Hq]. intros q0 Hq0. rewrite length_merge. apply Hl. right. exact Hq0.
Qed.

Lemma fold_merge_sound : forall fr fl col (f : positive -> nat * nat) l R,
  sat fr fl col R -> (forall q, In q l -> fr (col (fst (f q))) = fl (col (snd (f q)))) ->
  sat fr fl col (fold_left (fun R q => merge R (fst (f q)) (snd (f q))) l R).
Proof.
  induction l as [|q l IH]; intros R HR Hl; simpl; [exact HR|].
  apply IH; [|intros; apply Hl; right; assumption]. apply merge_sound; [exact HR|]. apply Hl. left. reflexivity.
Qed.

Lemma merges_unfold : forall R lm t bk fw,
  merges R lm t bk fw =
  fold_left (fun R q => merge R (fst ((fun q => (t, lab lm q)) q)) (snd ((fun q => (t, lab lm q)) q))) fw
    (fold_left (fun R q => merge R (fst ((fun q => (lab lm q, t)) q)) (snd ((fun q => (lab lm q, t)) q))) bk R).
Proof. reflexivity. Qed.

Lemma fold_merge_length : forall (f : positive -> nat * nat) l R,
  length (fold_left (fun R q => merge R (fst (f q)) (snd (f q))) l R) = length R.
Proof. induction l as [|q l IH]; intros R; simpl; [reflexivity|]. rewrite IH. apply length_merge. Qed.

Lemma merges_length : forall R lm t bk fw, length (merges R lm t bk fw) = length R.
Proof. intros. rewrite merges_unfold, !fold_merge_length. reflexivity. Qed.

Lemma merges_mono : forall R lm t bk fw i j, rget R i j = true -> rget (merges R lm t bk fw) i j = true.
Proof. intros. rewrite merges_unfold. apply fold_merge_mono. apply fold_merge_mono. assumption. Qed.

Lemma merges_sound : forall fr fl col R lm t bk fw, sat fr fl col R ->
  (forall p, In p bk -> fr (col (lab lm p)) = fl (col t)) ->
  (forall q, In q fw -> fr (col t) = fl (col (lab lm q))) -> sat fr fl col (merges R lm t bk fw).
Proof.
  intros. rewrite merges_unfold. apply fold_merge_sound; [apply fold_merge_sound|]; simpl; assumption.
Qed.

Lemma merges_bk : forall R lm t bk fw p, (forall p, In p bk -> lab lm p < length R) -> In p bk ->
  rget (merges R lm t bk fw) (lab lm p) t = true.
Proof.
  intros. rewrite merges_unfold. apply fold_merge_mono.
  apply (fold_merge_in (fun q => (lab lm q, t))); simpl; assumption.
Qed.

Lemma merges_fw : forall R lm t bk fw q, t < length R -> In q fw ->
  rget (merges R lm t bk fw) t (lab lm q) = true.
Proof.
  intros R lm t bk fw q Ht Hq. rewrite merges_unfold. apply (fold_merge_in (fun q => (t, lab lm q))); [|exact Hq].
  intros q0 _. rewrite fold_merge_length. exact Ht.
Qed.

(** ** The seen table *)

Definition InSeen (x : skey) (m : PM.t (list skey)) : Prop :=
  exists h b, PM.find h m = Some b /\ In x b.

Lemma InSeen_add : forall y x m h, InSeen y (PM.add h (x :: bucket m h) m) -> y = x \/ InSeen y m.
Proof.
  intros y x m h [h' [b [E Hy]]]. destruct (Pos.eq_dec h' h) as [->|Hne].
  - rewrite PM.gss in E. inversion E; subst. destruct Hy as [<-|Hy]; [left; reflexivity|right].
    unfold bucket in Hy. destruct (PM.find h m) as [b'|] eqn:Eb; [|destruct Hy].
    exists h, b'. auto.
  - rewrite PM.gso in E by exact Hne. right. exists h', b. auto.
Qed.

Lemma InSeen_empty : forall x, ~ InSeen x (PM.empty _).
Proof. intros x [h [b [E _]]]. rewrite PM.gempty in E. discriminate. Qed.

Lemma bucket_find_in : forall b x y, bucket_find b x = Some y -> In y b.
Proof.
  induction b as [|z b IH]; intros x y E; simpl in *; [discriminate|].
  destruct (skey_eqb x z); [inversion E; left; reflexivity|right; eapply IH; eassumption].
Qed.

Lemma seen_hit : forall n m h x r, seen_find n m h x r = SHit -> exists y, InSeen y m /\ dec n y = r.
Proof.
  intros n m h x r E. unfold seen_find in E.
  destruct (bucket_find (bucket m h) x) as [y|] eqn:Eb; [|discriminate].
  destruct (rst_eqb (dec n y) r) eqn:Er; [|discriminate].
  exists y. split; [|apply rst_eqb_eq; exact Er].
  apply bucket_find_in in Eb. unfold bucket in Eb. destruct (PM.find h m) as [b|] eqn:Ef; [|destruct Eb].
  exists h, b. auto.
Qed.

Section Sound.
Variables (n D P shard : nat).
Variable owners : list nat.
Hypothesis Hn : 1 <= n.
Hypothesis Hgeo : geo_ok D = true.
Variable tor : PArray.array (option (ctorus n)).
Variables mask gate : int.

Local Notation N := (D * D).
Local Notation walkf := (walk n D (images D) tor mask gate (mk_tbl D) (centre_order D) owners shard).
Local Notation nodeb := (node_body n D tor mask gate (mk_tbl D) (centre_order D)).
Local Notation nodea := (node_answer n D tor mask gate (mk_tbl D) (centre_order D)).
Local Notation claimf := (claim n D tor mask gate (mk_tbl D) (centre_order D)).
Local Notation tbl pos := (map (mk_entry D P) (seq pos (S (D * D) - pos))).

(** ** What a settled claim means *)

(** [col] (labels to tiles) tiles the DxD square with some labelling. *)
Definition tiles_lab (col : nat -> tile) : Prop :=
  exists F : nat -> nat -> nat, (forall r c, r < D -> c < D -> F r c < n) /\
    (forall r c, r < D -> S c < D -> right (col (F r c)) = left (col (F r (S c)))) /\
    (forall r c, S r < D -> c < D -> bottom (col (F r c)) = top (col (F (S r) c))).

(** Every tile set satisfying the equalities (H, V) that tiles the DxD square tiles the plane. *)
Definition Settled (H V : rel) : Prop :=
  forall col, sat right left col H -> sat bottom top col V -> tiles_lab col -> plane_n n col.

Definition ClosedInv (m : PM.t (list (rel * rel))) : Prop :=
  forall h b x, PM.find h m = Some b -> In x b -> Settled (fst x) (snd x).

Lemma ClosedInv_empty : ClosedInv (PM.empty _).
Proof. intros h b x E. rewrite PM.gempty in E. discriminate. Qed.

Lemma ClosedInv_add : forall m h H V, ClosedInv m -> Settled H V -> ClosedInv (PM.add h ((H, V) :: cbucket m h) m).
Proof.
  intros m h H V HC HS h' b x E Hx. destruct (Pos.eq_dec h' h) as [->|Hne].
  - rewrite PM.gss in E. inversion E; subst. destruct Hx as [<-|Hx]; [exact HS|].
    unfold cbucket in Hx. destruct (PM.find h m) eqn:Eb; [apply (HC _ _ _ Eb Hx)|destruct Hx].
  - rewrite PM.gso in E by exact Hne. apply (HC _ _ _ E Hx).
Qed.

Lemma closed_mem_sound : forall m h H V, ClosedInv m -> closed_mem m h H V = true -> Settled H V.
Proof.
  intros m h H V HC E. unfold closed_mem, cbucket in E. destruct (PM.find h m) as [b|] eqn:Eb; [|discriminate].
  apply existsb_exists in E as [[H' V'] [Hin Ex]]. apply andb_true_iff in Ex as [E1 E2].
  apply rel_eqb_eq in E1, E2. subst. apply (HC _ _ _ Eb Hin).
Qed.

Lemma settled_ok_sound : forall s tok H V, ClosedInv (w_closed s) -> settled_ok n tor s tok H V = true -> Settled H V.
Proof.
  intros s tok H V HC E. unfold settled_ok in E. destruct (PrimInt63.eqb tok 1).
  - apply (closed_mem_sound _ _ _ _ HC E).
  - intros col SH SV _. apply (torus_ok_plane n tor tok H V col E SH SV).
Qed.

Lemma refutes_rel_sound : forall H V, refutes_rel n D (mk_tbl D) (centre_order D) H V = true ->
  forall F, ltiling n (rget H) (rget V) D F -> False.
Proof.
  intros H V E F HF.
  exact (refute_top_sound n (rget H) (rget V) D (centre_order D) (4 * (n + 2) * (D * D)) (centre_order_spec D) E F HF).
Qed.

Lemma pairs_in : forall (H V : rel) (b : bool) (i j : nat), i < n -> j < n ->
  (if b then rget H i j else rget V i j) = false -> In (b, i, j) (pairs n H V).
Proof.
  intros H V b i j Hi Hj E. unfold pairs. apply in_or_app. destruct b; [left|right];
  apply in_flat_map; exists i; (split; [apply in_seq; lia|]); apply in_map; apply filter_In;
  (split; [apply in_seq; lia|rewrite E; reflexivity]).
Qed.

(** A closed claim: (H, V) admits no DxD square, and every one-merge superset is settled.
    A tile set satisfying (H, V) either has exactly these equalities, so it tiles no DxD
    square, or satisfies one more, and then a superset. *)
Lemma closed_sem : forall H V, refutes_rel n D (mk_tbl D) (centre_order D) H V = true ->
  (forall p, In p (pairs n H V) -> Settled (fst (sup H V p)) (snd (sup H V p))) -> Settled H V.
Proof.
  intros H V Er Hs col SH SV [F [HF1 [HF2 HF3]]].
  set (cr := fun p : bool * nat * nat => let '(b, i, j) := p in
               if b then Nat.eqb (right (col i)) (left (col j)) else Nat.eqb (bottom (col i)) (top (col j))).
  destruct (existsb cr (pairs n H V)) eqn:Ex.
  - apply existsb_exists in Ex as [[[b i] j] [Hin Ep]].
    apply (Hs _ Hin); [| |exists F; auto]; destruct b; simpl in *; apply Nat.eqb_eq in Ep;
      try (apply merge_sound; assumption); assumption.
  - exfalso. apply (refutes_rel_sound H V Er F). split; [exact HF1|split].
    + intros r c Hr Hc. destruct (rget H (F r c) (F r (S c))) eqn:EH; [reflexivity|]. exfalso.
      assert (Hin : In (true, F r c, F r (S c)) (pairs n H V)) by (apply pairs_in; auto; apply HF1; lia).
      rewrite <- not_true_iff_false in Ex. apply Ex. apply existsb_exists. exists (true, F r c, F r (S c)).
      split; [exact Hin|]. simpl. apply Nat.eqb_eq. apply HF2; assumption.
    + intros r c Hr Hc. destruct (rget V (F r c) (F (S r) c)) eqn:EV; [reflexivity|]. exfalso.
      assert (Hin : In (false, F r c, F (S r) c) (pairs n H V)) by (apply pairs_in; auto; apply HF1; lia).
      rewrite <- not_true_iff_false in Ex. apply Ex. apply existsb_exists. exists (false, F r c, F (S r) c).
      split; [exact Hin|]. simpl. apply Nat.eqb_eq. apply HF3; assumption.
Qed.

(** ** What the steps of the walk preserve *)

Definition Pres (s s' : wst) : Prop :=
  w_seen s' = w_seen s /\ w_rec s' = w_rec s /\ (ClosedInv (w_closed s) -> ClosedInv (w_closed s')).

Definition Same (s s' : wst) : Prop := w_seen s' = w_seen s /\ w_rec s' = w_rec s /\ w_closed s' = w_closed s.

Lemma Same_Pres : forall s s', Same s s' -> Pres s s'.
Proof. intros s s' [A [B C]]. split; [exact A|]. split; [exact B|]. rewrite C. auto. Qed.

Lemma Pres_refl : forall s, Pres s s.
Proof. intros s. split; [reflexivity|]. split; [reflexivity|auto]. Qed.

Lemma Pres_trans : forall s1 s2 s3, Pres s1 s2 -> Pres s2 s3 -> Pres s1 s3.
Proof.
  intros s1 s2 s3 [A1 [B1 C1]] [A2 [B2 C2]]. split; [congruence|]. split; [congruence|auto].
Qed.

Lemma rel_answer_same : forall s a b fr v s', rel_answer mask s a b = Some (fr, v, s') -> Same s s'.
Proof.
  intros s a b fr v s' E. unfold rel_answer in E.
  destruct (cread mask (w_rel s) (w_gen s) (w_rd s) a b) as [[[[fr0 v0] t] rd]|]; [|discriminate].
  inversion E; subst. repeat split.
Qed.

Lemma fin_answer_same : forall s a b fr v s', fin_answer mask s a b = Some (fr, v, s') -> Same s s'.
Proof.
  intros s a b fr v s' E. unfold fin_answer in E.
  destruct (cread mask (w_fin s) (w_gen s) (w_rd s) a b) as [[[[fr0 v0] t] rd]|]; [|discriminate].
  inversion E; subst. repeat split.
Qed.

Lemma gate_answer_same : forall vis s a b fr v s', gate_answer mask gate vis s a b = Some (fr, v, s') -> Same s s'.
Proof.
  intros vis s a b fr v s' E. unfold gate_answer in E.
  destruct (vis && PrimInt63.eqb gate 0); [inversion E; subst; repeat split|].
  destruct (cfind (w_gate s) mask (w_gen s) a b) as [[o i]|]; [|discriminate].
  destruct (PrimInt63.leb gate_flag _); [inversion E; subst; repeat split|].
  destruct (vis && _); [inversion E; subst; repeat split|].
  destruct (read_token (w_rd s)). inversion E; subst. repeat split.
Qed.

Lemma set_mark_same : forall s rd x, Same s (set_mark s rd x).
Proof. intros. repeat split. Qed.

Lemma mark_step_same : forall s ins s', mark_step s = (ins, s') -> Same s s'.
Proof.
  intros s ins s' E. unfold mark_step in E.
  destruct (PrimInt63.eqb (w_mark s) max_int); [inversion E; subst; repeat split|].
  destruct (PrimInt63.eqb (w_mark s) 1).
  { destruct (read_token (w_rd s)). inversion E; subst. repeat split. }
  destruct (PrimInt63.eqb (w_mark s) 0); inversion E; subst; repeat split.
Qed.

Lemma add_closed_pres : forall s h H V, Settled H V -> Pres s (add_closed s h H V).
Proof.
  intros s h H V HS. split; [reflexivity|]. split; [reflexivity|]. intros HC. apply ClosedInv_add; assumption.
Qed.

Lemma sup_answer_pres : forall cl, (forall tok H V s s', cl tok H V s = Some s' -> Pres s s') ->
  forall H V s tok s', sup_answer n mask gate cl H V s = Some (tok, s') -> Pres s s'.
Proof.
  intros cl Hcl H V s tok s' E. unfold sup_answer in E.
  destruct (rel_answer mask s _ _) as [[[fr t0] s1]|] eqn:E1; [|discriminate].
  apply rel_answer_same, Same_Pres in E1.
  destruct fr.
  - destruct (PrimInt63.eqb t0 0); [discriminate|].
    destruct (cl t0 H V s1) as [s2|] eqn:E2; [|discriminate]. inversion E; subst.
    apply (Pres_trans _ _ _ E1 (Hcl _ _ _ _ _ E2)).
  - destruct (negb (PrimInt63.eqb t0 0)); [inversion E; subst; exact E1|].
    destruct (gate_answer mask gate false s1 _ _) as [[[fr2 g] s2]|] eqn:E2; [|discriminate].
    apply gate_answer_same, Same_Pres in E2.
    destruct (PrimInt63.eqb g 0); [discriminate|]. destruct fr2.
    + destruct (cl g H V s2) as [s3|] eqn:E3; [|discriminate]. inversion E; subst.
      apply (Pres_trans _ _ _ (Pres_trans _ _ _ E1 E2) (Hcl _ _ _ _ _ E3)).
    + inversion E; subst. apply (Pres_trans _ _ _ E1 E2).
Qed.

Lemma supers_spec : forall cl, (forall tok H V s s', cl tok H V s = Some s' -> Pres s s') ->
  forall H V ps done s s', supers n tor mask gate cl H V ps done s = Some s' ->
  Pres s s' /\ (ClosedInv (w_closed s) -> (forall d, In d done -> Settled (fst d) (snd d)) ->
                forall p, In p ps -> Settled (fst (sup H V p)) (snd (sup H V p))).
Proof.
  intros cl Hcl H V. induction ps as [|p ps IH]; intros done s s' E; cbn [supers] in E.
  - inversion E; subst. split; [apply Pres_refl|intros _ _ p []].
  - destruct (sup H V p) as [H' V'] eqn:Ep.
    destruct (existsb (fun x => rel_eqb (fst x) H' && rel_eqb (snd x) V') done) eqn:Ex.
    + destruct (IH done s s' E) as [P1 P2]. split; [exact P1|].
      intros HC Hd q [<-|Hq]; [|apply P2; assumption]. rewrite Ep. simpl.
      apply existsb_exists in Ex as [[H1 V1] [Hin E1]]. apply andb_true_iff in E1 as [E1 E2].
      apply rel_eqb_eq in E1, E2. subst. apply (Hd _ Hin).
    + destruct (sup_answer n mask gate cl H' V' s) as [[tok s1]|] eqn:E1; [|discriminate].
      pose proof (sup_answer_pres cl Hcl H' V' s tok s1 E1) as P1.
      destruct (settled_ok n tor s1 tok H' V') eqn:Es; [|discriminate].
      destruct (IH ((H', V') :: done) s1 s' E) as [P2 P3].
      split; [apply (Pres_trans _ _ _ P1 P2)|].
      intros HC Hd.
      assert (HC1 : ClosedInv (w_closed s1)) by (apply P1; exact HC).
      pose proof (settled_ok_sound _ _ _ _ HC1 Es) as HS.
      intros q [<-|Hq]; [rewrite Ep; exact HS|].
      apply (P3 HC1); [|exact Hq]. intros d [<-|Hdd]; [exact HS|apply Hd; exact Hdd].
Qed.

Lemma claim_pres : forall fuel tok H V s s', claimf fuel tok H V s = Some s' -> Pres s s'.
Proof.
  induction fuel as [|f IH]; intros tok H V s s' E; cbn [claim] in E; [discriminate|].
  destruct (PrimInt63.eqb tok 1); [|inversion E; subst; apply Pres_refl].
  destruct (refutes_rel n D (mk_tbl D) (centre_order D) H V) eqn:Er; [|discriminate].
  destruct (supers n tor mask gate (claimf f) H V (pairs n H V) [] s) as [s1|] eqn:E1; [|discriminate].
  inversion E; subst. clear E.
  generalize (chash (rbits n H) (rbits n V)) as h. intros h.
  destruct (supers_spec _ IH H V _ [] s s1 E1) as [[A [B C]] D2].
  split; [exact A|]. split; [exact B|]. intros HC. cbn [w_closed add_closed set_closed].
  apply ClosedInv_add; [apply C; exact HC|].
  apply closed_sem; [exact Er|]. apply (D2 HC). intros d [].
Qed.

Lemma fresh_claim_pres : forall fr tok H V s s',
  fresh_claim n D tor mask gate (mk_tbl D) (centre_order D) fr tok H V s = Some s' -> Pres s s'.
Proof.
  intros fr tok H V s s' E. unfold fresh_claim in E.
  destruct (fr && negb (PrimInt63.eqb tok 0)); [apply (claim_pres _ _ _ _ _ _ E)|inversion E; subst; apply Pres_refl].
Qed.

Lemma node_answer_pres : forall e same H V s ans s', nodea e same H V s = Some (ans, s') -> Pres s s'.
Proof.
  intros e same H V s ans s' E. unfold node_answer in E.
  destruct (if same && e_deep e then _ else _) as [[[fr1 a1] s1]|] eqn:E1; [|discriminate].
  assert (P1 : Pres s s1).
  { destruct (same && e_deep e); [inversion E1; subst; apply Pres_refl|apply Same_Pres; apply (rel_answer_same _ _ _ _ _ _ E1)]. }
  destruct (fresh_claim _ _ _ _ _ _ _ fr1 a1 H V s1) as [s2|] eqn:E2; [|discriminate].
  pose proof (fresh_claim_pres _ _ _ _ _ _ E2) as P2.
  destruct (if PrimInt63.eqb a1 0 then _ else _) as [[[fr3 a3] s3]|] eqn:E3; [|discriminate].
  assert (P3 : Pres s2 s3).
  { destruct (PrimInt63.eqb a1 0); [apply Same_Pres; apply (gate_answer_same _ _ _ _ _ _ _ E3)|inversion E3; subst; apply Pres_refl]. }
  destruct (fresh_claim _ _ _ _ _ _ _ fr3 a3 H V s3) as [s4|] eqn:E4; [|discriminate].
  pose proof (fresh_claim_pres _ _ _ _ _ _ E4) as P4.
  destruct (if PrimInt63.eqb a3 0 && e_full e then _ else _) as [[[fr5 a5] s5]|] eqn:E5; [|discriminate].
  assert (P5 : Pres s4 s5).
  { destruct (PrimInt63.eqb a3 0 && e_full e); [apply Same_Pres; apply (fin_answer_same _ _ _ _ _ _ E5)|inversion E5; subst; apply Pres_refl]. }
  destruct (fresh_claim _ _ _ _ _ _ _ fr5 a5 H V s5) as [s6|] eqn:E6; [|discriminate].
  pose proof (fresh_claim_pres _ _ _ _ _ _ E6) as P6.
  inversion E; subst.
  repeat (eapply Pres_trans; [eassumption|]). apply Pres_refl.
Qed.


(** ** The node invariant *)

Definition pvalid (col : nat -> tile) (pre : list nat) : Prop :=
  forall p q, p < length pre -> q < length pre ->
    (hadj D p q = true -> right (col (nth p pre 0)) = left (col (nth q pre 0))) /\
    (vadj D p q = true -> bottom (col (nth p pre 0)) = top (col (nth q pre 0))).

(** The invariant of every node of the walk. *)
Record NodeInv (pos : nat) (pre : list nat) (k : nat) (lm : PM.t nat) (H V : rel) : Prop := {
  ni_len : length pre = pos;
  ni_pos : pos <= N;
  ni_lab : forall q, q < pos -> lab lm (pk q) = nth q pre 0;
  ni_lt : forall x, In x pre -> x < n;
  ni_canon : canon 0 pre;
  ni_k : cnext 0 pre = k;
  ni_lH : length H = n;
  ni_lV : length V = n;
  ni_sound : forall col, pvalid col pre -> sat right left col H /\ sat bottom top col V;
  ni_cH : forall p q, p < pos -> q < pos -> hadj D p q = true -> rget H (nth p pre 0) (nth q pre 0) = true;
  ni_cV : forall p q, p < pos -> q < pos -> vadj D p q = true -> rget V (nth p pre 0) (nth q pre 0) = true }.

Lemma ni_root : NodeInv 0 [] 0 (PM.empty _) (rempty n) (rempty n).
Proof.
  constructor; simpl; try lia; try tauto.
  - apply length_rempty.
  - apply length_rempty.
  - intros col _. split; apply sat_rempty.
Qed.

Lemma in_nb : forall (f : nat -> nat -> bool) pos x,
  In x (map pk (filter (fun p => f p pos) (seq 0 pos))) -> exists p, x = pk p /\ p < pos /\ f p pos = true.
Proof.
  intros f pos x Hx. apply in_map_iff in Hx as [p [<- Hp]]. apply filter_In in Hp as [Hp Hf].
  apply in_seq in Hp. exists p. split; [reflexivity|split; [lia|exact Hf]].
Qed.

Lemma in_nb' : forall (f : nat -> nat -> bool) pos x,
  In x (map pk (filter (fun q => f pos q) (seq 0 pos))) -> exists q, x = pk q /\ q < pos /\ f pos q = true.
Proof.
  intros f pos x Hx. apply in_map_iff in Hx as [p [<- Hp]]. apply filter_In in Hp as [Hp Hf].
  apply in_seq in Hp. exists p. split; [reflexivity|split; [lia|exact Hf]].
Qed.

Lemma nb_in : forall (f : nat -> nat -> bool) pos p, p < pos -> f p pos = true ->
  In (pk p) (map pk (filter (fun p => f p pos) (seq 0 pos))).
Proof. intros. apply in_map. apply filter_In. split; [apply in_seq; lia|assumption]. Qed.

Lemma nb_in' : forall (f : nat -> nat -> bool) pos q, q < pos -> f pos q = true ->
  In (pk q) (map pk (filter (fun q => f pos q) (seq 0 pos))).
Proof. intros. apply in_map. apply filter_In. split; [apply in_seq; lia|assumption]. Qed.

Lemma pvalid_prefix : forall col pre t, pvalid col (pre ++ [t]) -> pvalid col pre.
Proof.
  intros col pre t HP p q Hp Hq. specialize (HP p q ltac:(rewrite length_app; simpl; lia) ltac:(rewrite length_app; simpl; lia)).
  rewrite !app_nth1 in HP by lia. exact HP.
Qed.

Lemma ni_child : forall pos pre k lm H V t, NodeInv pos pre k lm H V -> pos < N -> t <= k -> t < n ->
  NodeInv (S pos) (pre ++ [t]) (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
    (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
    (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))).
Proof.
  intros pos pre k lm H V t HI Hpos Htk Htn. destruct HI.
  assert (Hlast : nth pos (pre ++ [t]) 0 = t).
  { rewrite app_nth2 by lia. rewrite ni_len0, Nat.sub_diag. reflexivity. }
  assert (Hold : forall q, q < pos -> nth q (pre ++ [t]) 0 = nth q pre 0).
  { intros q Hq. apply app_nth1. lia. }
  assert (Hlabs : forall q, q < pos -> nth q pre 0 < n).
  { intros q Hq. apply ni_lt0. apply nth_In. lia. }
  constructor.
  - rewrite length_app. simpl. lia.
  - lia.
  - intros q Hq. unfold lab. destruct (Nat.eq_dec q pos) as [->|Hne].
    + rewrite PM.gss. rewrite Hlast. reflexivity.
    + rewrite PM.gso by (intros E; apply Hne, pk_inj, E). fold (lab lm (pk q)).
      rewrite ni_lab0 by lia. rewrite Hold by lia. reflexivity.
  - intros x Hx. apply in_app_or in Hx as [Hx|[<-|[]]]; [apply ni_lt0; exact Hx|exact Htn].
  - apply canon_app. split; [exact ni_canon0|]. rewrite ni_k0. simpl. auto.
  - rewrite cnext_app, ni_k0. reflexivity.
  - rewrite merges_length. exact ni_lH0.
  - rewrite merges_length. exact ni_lV0.
  - intros col HP. destruct (ni_sound0 col (pvalid_prefix col pre t HP)) as [S1 S2].
    assert (Hlen : length (pre ++ [t]) = S pos) by (rewrite length_app; simpl; lia).
    split.
    + apply merges_sound; [exact S1| |].
      * intros x Hx. apply in_nb in Hx as [p [-> [Hp Hf]]]. rewrite ni_lab0 by exact Hp.
        specialize (HP p pos ltac:(lia) ltac:(lia)). rewrite Hlast, Hold in HP by exact Hp. apply HP. exact Hf.
      * intros x Hx. apply in_nb' in Hx as [q [-> [Hq Hf]]]. rewrite ni_lab0 by exact Hq.
        specialize (HP pos q ltac:(lia) ltac:(lia)). rewrite Hlast, Hold in HP by exact Hq. apply HP. exact Hf.
    + apply merges_sound; [exact S2| |].
      * intros x Hx. apply in_nb in Hx as [p [-> [Hp Hf]]]. rewrite ni_lab0 by exact Hp.
        specialize (HP p pos ltac:(lia) ltac:(lia)). rewrite Hlast, Hold in HP by exact Hp. apply HP. exact Hf.
      * intros x Hx. apply in_nb' in Hx as [q [-> [Hq Hf]]]. rewrite ni_lab0 by exact Hq.
        specialize (HP pos q ltac:(lia) ltac:(lia)). rewrite Hlast, Hold in HP by exact Hq. apply HP. exact Hf.
  - intros p q Hp Hq E.
    destruct (Nat.eq_dec p pos) as [->|Hp']; destruct (Nat.eq_dec q pos) as [->|Hq'].
    + rewrite hadj_irrefl in E. discriminate.
    + rewrite Hlast, Hold by lia. rewrite <- ni_lab0 by lia.
      apply merges_fw; [rewrite ni_lH0; exact Htn|]. apply nb_in'; [lia|exact E].
    + rewrite Hlast, Hold by lia. rewrite <- ni_lab0 by lia.
      apply merges_bk; [|apply nb_in; [lia|exact E]].
      intros x Hx. apply in_nb in Hx as [p' [-> [Hp'' _]]]. rewrite ni_lab0, ni_lH0 by exact Hp''. apply Hlabs. exact Hp''.
    + rewrite !Hold by lia. apply merges_mono. apply ni_cH0; [lia|lia|exact E].
  - intros p q Hp Hq E.
    destruct (Nat.eq_dec p pos) as [->|Hp']; destruct (Nat.eq_dec q pos) as [->|Hq'].
    + rewrite vadj_irrefl in E. discriminate.
    + rewrite Hlast, Hold by lia. rewrite <- ni_lab0 by lia.
      apply merges_fw; [rewrite ni_lV0; exact Htn|]. apply nb_in'; [lia|exact E].
    + rewrite Hlast, Hold by lia. rewrite <- ni_lab0 by lia.
      apply merges_bk; [|apply nb_in; [lia|exact E]].
      intros x Hx. apply in_nb in Hx as [p' [-> [Hp'' _]]]. rewrite ni_lab0, ni_lV0 by exact Hp''. apply Hlabs. exact Hp''.
    + rewrite !Hold by lia. apply merges_mono. apply ni_cV0; [lia|lia|exact E].
Qed.

(** A node stored in the seen table, with the property [Q] of its labels. *)
Definition Stored (Q : list nat -> Prop) (x : skey) : Prop :=
  exists pos pre k lm H V nu inv, NodeInv pos pre k lm H V /\ pos < N /\ perm_ok n k nu inv = true /\
    dec n x = mkR (pk pos) k (map (fun l => nth l nu 0) (map (lab lm) (map pk (frontier D pos))))
                  (rrename n inv H) (rrename n inv V) /\ Q pre.

Lemma Stored_weaken : forall (Q1 Q2 : list nat -> Prop) x, (forall l, Q1 l -> Q2 l) -> Stored Q1 x -> Stored Q2 x.
Proof.
  intros Q1 Q2 x HQ [pos [pre [k [lm [H [V [nu [inv [A1 [A2 [A3 [A4 A5]]]]]]]]]]]].
  exists pos, pre, k, lm, H, V, nu, inv.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. apply HQ; exact A5.
Qed.

Lemma tbl_cons : forall pos, pos <= N -> tbl pos = mk_entry D P pos :: tbl (S pos).
Proof. intros pos Hpos. rewrite seq_S_cons by exact Hpos. reflexivity. Qed.

Lemma seq_labels : forall k t, In t (seq 0 (S (Nat.min k (n - 1)))) -> t <= k /\ t < n.
Proof. intros k t Ht. apply in_seq in Ht. lia. Qed.

Lemma stored_here_eq : forall pos pre k lm H V r, NodeInv pos pre k lm H V -> pos < N ->
  rst_of n (mk_entry D P pos) k lm H V = Some r -> forall xx, rst_eqb (dec n xx) r = true ->
  Stored (fun pre' => pre' = pre) xx.
Proof.
  intros pos pre k lm H V r HI Hpos Er xx Ed.
  destruct (rst_of_spec _ _ _ _ _ _ _ Er) as [nu [inv [Hp ->]]].
  exists pos, pre, k, lm, H, V, nu, inv.
  split; [exact HI|]. split; [lia|]. split; [exact Hp|]. split; [|reflexivity].
  apply rst_eqb_eq in Ed. rewrite Ed. reflexivity.
Qed.

Lemma stored_here : forall pos pre k lm H V r, NodeInv pos pre k lm H V -> pos < N ->
  rst_of n (mk_entry D P pos) k lm H V = Some r -> forall xx, rst_eqb (dec n xx) r = true ->
  Stored (fun pre' => firstn pos pre' = pre /\ pos <= length pre') xx.
Proof.
  intros pos pre k lm H V r HI Hpos Er xx Ed.
  pose proof (ni_len _ _ _ _ _ _ HI) as Hl.
  apply (Stored_weaken (fun pre' => pre' = pre)); [|apply (stored_here_eq pos pre k lm H V r HI Hpos Er xx Ed)].
  intros l ->. split; [apply firstn_all2; lia|lia].
Qed.


Lemma full_lt : forall pos, pos <= N -> e_full (mk_entry D P pos) = false -> pos < N.
Proof. intros pos Hpos E. cbn in E. apply Nat.eqb_neq in E. lia. Qed.

(** ** Frames: what a walk leaves in the state *)

Definition FrameW (pos : nat) (pre : list nat) (s s' : wst) : Prop :=
  (ClosedInv (w_closed s) -> ClosedInv (w_closed s')) /\ (exists X, w_rec s' = X ++ w_rec s) /\
  (forall x, InSeen x (w_seen s') -> InSeen x (w_seen s) \/ Stored (fun pre' => firstn pos pre' = pre /\ pos <= length pre') x).

Lemma Pres_FrameW : forall pos pre s s', Pres s s' -> FrameW pos pre s s'.
Proof.
  intros pos pre s s' [A [B C]]. split; [exact C|]. split; [exists []; rewrite B; reflexivity|].
  intros x Hx. left. rewrite <- A. exact Hx.
Qed.

Lemma FrameW_trans : forall pos pre s1 s2 s3, FrameW pos pre s1 s2 -> FrameW pos pre s2 s3 -> FrameW pos pre s1 s3.
Proof.
  intros pos pre s1 s2 s3 [A1 [[X1 B1] C1]] [A2 [[X2 B2] C2]]. split; [auto|]. split.
  - exists (X2 ++ X1). rewrite B2, B1, app_assoc. reflexivity.
  - intros x Hx. destruct (C2 x Hx) as [H|H]; [|right; exact H]. apply C1. exact H.
Qed.

Lemma FrameW_weaken : forall pos pre t s s', length pre = pos ->
  FrameW (S pos) (pre ++ [t]) s s' -> FrameW pos pre s s'.
Proof.
  intros pos pre t s s' Hl [A [B C]]. split; [exact A|]. split; [exact B|].
  intros x Hx. destruct (C x Hx) as [H|H]; [left; exact H|right].
  revert H. apply Stored_weaken. intros l [E1 E2]. split; [|lia]. apply (firstn_prefix l pre t pos E1 Hl).
Qed.

Lemma seen_insert_frame : forall pos pre s hh xx,
  Stored (fun pre' => firstn pos pre' = pre /\ pos <= length pre') xx ->
  FrameW pos pre s (set_seen s (PM.add hh (xx :: bucket (w_seen s) hh) (w_seen s))).
Proof.
  intros pos pre s hh xx Hst. split; [auto|]. split; [exists []; reflexivity|].
  intros x Hx. cbn [w_seen set_seen] in Hx. destruct (InSeen_add x xx (w_seen s) hh Hx) as [->|H].
  - right. exact Hst.
  - left. exact H.
Qed.

Lemma loop_frame : forall (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) pos pre k lm H V ts s s2,
  NodeInv pos pre k lm H V -> pos < N ->
  (forall t, In t ts -> t <= k /\ t < n) ->
  (forall sm t s s', t <= k -> t < n -> w sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (pre ++ [t]) s s') ->
  loop_children w (mk_entry D P pos) k lm H V ts s = Some s2 -> FrameW pos pre s s2.
Proof.
  intros w pos pre k lm H V ts. induction ts as [|t ts IH]; intros s s2 HI Hpos Hts Hw E; cbn [loop_children] in E.
  - inversion E; subst. apply Pres_FrameW, Pres_refl.
  - destruct (w _ _ _ _ _ s) as [s'|] eqn:Ew; [|discriminate].
    destruct (Hts t (or_introl eq_refl)) as [Htk Htn].
    apply (FrameW_trans _ _ _ s'); [|apply (IH s' s2 HI Hpos (fun t0 H0 => Hts t0 (or_intror H0)) Hw E)].
    apply (FrameW_weaken pos pre t); [apply (ni_len _ _ _ _ _ _ HI)|]. apply (Hw _ t s s' Htk Htn Ew).
Qed.

Ltac dmatch E x := match type of E with context [match ?m with Some _ => _ | None => _ end] =>
  destruct m as [x|] eqn:?; [|discriminate] end.

Lemma node_frame : forall (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) pos pre same k lm H V s s',
  NodeInv pos pre k lm H V ->
  (forall sm t s s', t <= k -> t < n -> w sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (pre ++ [t]) s s') ->
  nodeb w (mk_entry D P pos) same k lm H V s = Some s' -> FrameW pos pre s s'.
Proof.
  intros w pos pre same k lm H V s s' HI Hw E. unfold node_body in E.
  destruct (nodea (mk_entry D P pos) same H V s) as [[ans s6]|] eqn:Ea; [|discriminate].
  pose proof (node_answer_pres _ _ _ _ _ _ _ Ea) as P6.
  destruct (negb (PrimInt63.eqb ans 0)).
  { destruct (settled_ok n tor s6 ans H V); [|discriminate]. inversion E; subst. apply Pres_FrameW; exact P6. }
  destruct (e_full (mk_entry D P pos)) eqn:Efull; [discriminate|].
  pose proof (full_lt pos (ni_pos _ _ _ _ _ _ HI) Efull) as Hpos.
  destruct (rst_of n (mk_entry D P pos) k lm H V) as [r|] eqn:Er; [|discriminate].
  cbv zeta in E. generalize dependent E. generalize (enc n r) as xx. intros xx.
  generalize (skey_hash xx) as hh. intros hh E.
  destruct (seen_find n (w_seen s6) hh xx r); try discriminate.
  { inversion E; subst. apply Pres_FrameW; exact P6. }
  destruct (mark_step s6) as [ins s7] eqn:Em.
  pose proof (Same_Pres _ _ (mark_step_same _ _ _ Em)) as P7.
  apply (FrameW_trans _ _ _ s7); [apply Pres_FrameW; exact (Pres_trans _ _ _ P6 P7)|].
  destruct ins.
  - destruct (rst_eqb (dec n xx) r) eqn:Ed; [|discriminate].
    apply (FrameW_trans _ _ _ _ _ (seen_insert_frame pos pre s7 hh xx (stored_here pos pre k lm H V r HI Hpos Er xx Ed))).
    apply (loop_frame w pos pre k lm H V _ _ s' HI Hpos (seq_labels k) Hw E).
  - apply (loop_frame w pos pre k lm H V _ _ s' HI Hpos (seq_labels k) Hw E).
Qed.

Lemma clear_frame : forall pos pre s s', w_seen s' = PM.empty _ -> (ClosedInv (w_closed s) -> ClosedInv (w_closed s')) ->
  (exists X, w_rec s' = X ++ w_rec s) -> FrameW pos pre s s'.
Proof.
  intros pos pre s s' E A B. split; [exact A|]. split; [exact B|].
  intros x Hx. rewrite E in Hx. destruct (InSeen_empty x Hx).
Qed.

Lemma walk_eq : forall fuel e tbl' sm k lm H V s,
  walkf (S fuel) (e :: tbl') sm k lm H V s =
  if sym_skip (images D) (e_key e) lm then Some s else
  if e_reset e then
    (if Nat.eqb (nth (List.length (w_rec s)) owners 0) shard
     then (let '(tok, rd) := read_token (w_rd (clear (push_rec s (map (lab lm) (e_pre e))))) in
           option_map clear (nodeb (walkf fuel tbl') e false k lm H V
             (set_mark (clear (push_rec s (map (lab lm) (e_pre e)))) rd tok)))
     else Some (clear (push_rec s (map (lab lm) (e_pre e)))))
  else nodeb (walkf fuel tbl') e sm k lm H V s.
Proof. reflexivity. Qed.

Lemma walk_frame : forall fuel pos pre sm k lm H V s s',
  NodeInv pos pre k lm H V -> walkf fuel (tbl pos) sm k lm H V s = Some s' -> FrameW pos pre s s'.
Proof.
  induction fuel as [|fuel IH]; intros pos pre sm k lm H V s s' HI E; [discriminate|].
  pose proof (ni_pos _ _ _ _ _ _ HI) as Hpos.
  rewrite tbl_cons, walk_eq in E by exact Hpos.
  change (e_key (mk_entry D P pos)) with (pk pos) in E.
  destruct (sym_skip (images D) (pk pos) lm); [inversion E; subst; apply Pres_FrameW, Pres_refl|].
  assert (Hw : forall sm t s s', t <= k -> t < n -> walkf fuel (tbl (S pos)) sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (pre ++ [t]) s s').
  { intros sm0 t s0 s0' Htk Htn Ew.
    destruct (Nat.eq_dec pos N) as [Ep|Ep].
    - exfalso. rewrite Ep, Nat.sub_diag in Ew. destruct fuel; discriminate.
    - eapply IH; [exact (ni_child pos pre k lm H V t HI ltac:(lia) Htk Htn)|exact Ew]. }
  change (e_reset (mk_entry D P pos)) with (is_reset P pos) in E.
  destruct (is_reset P pos).
  - set (s0 := clear (push_rec s _)) in E.
    assert (F0 : FrameW pos pre s s0).
    { apply clear_frame; [reflexivity|auto|]. exists [map (lab lm) (e_pre (mk_entry D P pos))]. reflexivity. }
    destruct (Nat.eqb _ shard).
    + destruct (read_token (w_rd s0)) as [tok rd].
      destruct (nodeb (walkf fuel (tbl (S pos))) _ false k lm H V (set_mark s0 rd tok)) as [s1|] eqn:E1; [|discriminate].
      cbn [option_map] in E. inversion E; subst. clear E.
      apply (FrameW_trans _ _ _ s0 _ F0).
      apply (FrameW_trans _ _ _ (set_mark s0 rd tok)); [apply Pres_FrameW, Same_Pres, set_mark_same|].
      apply (FrameW_trans _ _ _ s1); [apply (node_frame _ pos pre false k lm H V _ s1 HI Hw E1)|].
      apply clear_frame; [reflexivity|auto|exists []; reflexivity].
    + inversion E; subst. exact F0.
  - apply (node_frame _ pos pre sm k lm H V s s' HI Hw E).
Qed.


(** ** Following the path of one labelling *)

Section Path.
Variables (L : list nat) (col : nat -> tile).
Hypothesis HL : length L = N.
Hypothesis HLn : forall x, In x L -> x < n.
Hypothesis HLc : canon 0 L.
Hypothesis Hval : valid D col L.
Hypothesis IH : forall L' col', length L' = N -> (forall x, In x L' -> x < n) -> canon 0 L' ->
  rank n L' < rank n L -> valid D col' L' -> plane_n n col'.

(** Seen keys come from nodes left of L's path, or from nodes on it above the current position. *)
Definition SeenInv (pos : nat) (m : PM.t (list skey)) : Prop :=
  forall x, InSeen x m -> Stored (fun pre' => lexlt pre' (firstn (length pre') L) \/
                                             (pre' = firstn (length pre') L /\ length pre' < pos)) x.

(** L's prefix was recorded at a reset node that this shard leaves to another one. *)
Definition Deferred (r : list (list nat)) : Prop :=
  exists X rest, r = X ++ firstn P L :: rest /\ Nat.eqb (nth (length rest) owners 0) shard = false.

Lemma Deferred_app : forall Y r, Deferred r -> Deferred (Y ++ r).
Proof. intros Y r [X [rest [E F]]]. exists (Y ++ X), rest. rewrite E, app_assoc. split; [reflexivity|exact F]. Qed.

Lemma pvalid_L : forall pos, pos <= N -> pvalid col (firstn pos L).
Proof.
  intros pos Hpos p q Hp Hq. rewrite length_firstn in Hp, Hq.
  rewrite !nth_firstn_lt by lia. apply Hval; lia.
Qed.

Lemma Lnth_lt : forall p, nth p L 0 < n.
Proof.
  intros p. destruct (Nat.lt_ge_cases p (length L)).
  - apply HLn. apply nth_In. exact H.
  - rewrite nth_overflow by exact H. lia.
Qed.

(** *** Symmetric skips *)

Lemma skipn_cons_nth : forall (l : list nat) j, j < length l -> skipn j l = nth j l 0 :: skipn (S j) l.
Proof.
  induction l as [|x l IHl]; intros j Hj; simpl in *; [lia|].
  destruct j; [reflexivity|]. simpl. apply IHl. lia.
Qed.

Lemma cst_app : forall xs ys m0 a0, cst m0 a0 (xs ++ ys) = cst (fst (cst m0 a0 xs)) (snd (cst m0 a0 xs)) ys.
Proof.
  induction xs as [|z xs IHx]; intros ys m0 a0; simpl; [reflexivity|].
  destruct (rn_step z m0 a0) as [[? ?] ?]. apply IHx.
Qed.

Lemma symloop_spec : forall pos lm (im M : list nat), pos <= length L ->
  (forall q, q < pos -> lab lm (pk q) = nth q L 0) ->
  length im = length M -> (forall i, i < length im -> nth i M 0 = nth (nth i im 0) L 0) ->
  forall rest j m a, rest = skipn j im ->
  (m, a) = cst 0 [] (firstn j M) -> firstn j (canon_aux 0 [] M) = firstn j L ->
  symloop (pk pos) lm (map pk rest) (pk j) m a = true ->
  exists j', j' < pos /\ j' < length M /\ firstn j' (canon_aux 0 [] M) = firstn j' L /\
             nth j' (canon_aux 0 [] M) 0 < nth j' L 0.
Proof.
  intros pos lm im M HposL Hlab Hlen HM. induction rest as [|q rest IHr]; intros j m a Er Hst Hpre E;
    cbn [map symloop] in E; [discriminate|].
  rewrite !pk_ltb in E.
  destruct (Nat.ltb_spec j pos) as [Hjp|]; [|discriminate]. destruct (Nat.ltb_spec q pos) as [Hqp|]; [|discriminate].
  cbn [andb] in E.
  assert (Hjl : j < length im).
  { destruct (Nat.lt_ge_cases j (length im)); [assumption|]. rewrite skipn_all2 in Er by assumption. discriminate. }
  rewrite skipn_cons_nth in Er by exact Hjl. injection Er as Eq Erest.
  rewrite Hlab in E by exact Hqp. rewrite Hlab in E by exact Hjp.
  assert (EM : nth j M 0 = nth q L 0) by (rewrite HM by exact Hjl; rewrite Eq; reflexivity).
  rewrite <- EM in E.
  assert (Ecan : canon_aux 0 [] M = canon_aux 0 [] (firstn j M) ++ canon_aux m a (skipn j M)).
  { rewrite <- (firstn_skipn j M) at 1. rewrite canon_aux_app. rewrite <- Hst. reflexivity. }
  rewrite (skipn_cons_nth M j) in Ecan by lia.
  destruct (rn_step (nth j M 0) m a) as [[x m'] a'] eqn:Ern.
  assert (Ex : nth j (canon_aux 0 [] M) 0 = x).
  { rewrite Ecan. cbn [canon_aux]. rewrite Ern.
    rewrite app_nth2 by (rewrite length_canon_aux, length_firstn; lia).
    rewrite length_canon_aux, length_firstn, Nat.min_l by lia. rewrite Nat.sub_diag. reflexivity. }
  destruct (Nat.ltb_spec x (nth j L 0)) as [Hlt|Hge].
  - exists j. split; [exact Hjp|]. split; [lia|]. split; [exact Hpre|]. rewrite Ex. exact Hlt.
  - destruct (Nat.ltb_spec (nth j L 0) x) as [|Hle]; [discriminate|].
    rewrite pk_succ in E.
    apply (IHr (S j) m' a' Erest); [| |exact E].
    + rewrite (firstn_S_nth M j) by lia. rewrite cst_app, <- Hst. cbn [fst snd cst]. rewrite Ern. reflexivity.
    + rewrite (firstn_S_nth L j) by lia. rewrite (firstn_S_nth (canon_aux 0 [] M) j) by (rewrite length_canon_aux; lia).
      rewrite Hpre, Ex. f_equal. f_equal. lia.
Qed.

Lemma nth_image : forall g p, p < N ->
  nth p (image D g) 0 = pos_of D (symf D (fst (fst g)) (snd (fst g)) (snd g) (cell D p)).
Proof.
  intros [[sw fr] fc] p Hp. unfold image. apply nth_map_seq. exact Hp.
Qed.

Lemma length_image : forall g, length (image D g) = N.
Proof. intros [[sw fr] fc]. unfold image. rewrite length_map, length_seq. reflexivity. Qed.

Lemma sym_skip_plane : forall pos lm, pos <= N -> (forall q, q < pos -> lab lm (pk q) = nth q L 0) ->
  sym_skip (images D) (pk pos) lm = true -> plane_n n col.
Proof.
  intros pos lm Hpos Hlab E. unfold sym_skip in E. apply existsb_exists in E as [img [Himg E]].
  unfold images in Himg. apply in_map_iff in Himg as [g [<- Hg]].
  set (im := image D g) in *.
  set (M := map (fun i => nth (nth i im 0) L 0) (seq 0 N)).
  assert (HlenM : length M = N) by (unfold M; rewrite length_map, length_seq; reflexivity).
  assert (Hlenim : length im = N) by apply length_image.
  assert (HM : forall i, i < length im -> nth i M 0 = nth (nth i im 0) L 0).
  { intros i Hi. unfold M. apply (nth_map_seq (fun i => nth (nth i im 0) L 0)). lia. }
  destruct (symloop_spec pos lm im M ltac:(lia) Hlab ltac:(lia) HM im 0 0 [] eq_refl eq_refl eq_refl E)
    as [j [Hjp [HjM [Hpre Hlt]]]].
  assert (HMn : forall x, In x M -> x < n).
  { intros x Hx. unfold M in Hx. apply in_map_iff in Hx as [i [<- _]]. apply Lnth_lt. }
  destruct (canon_rename n M HMn) as [rho [Erho [Hcan [Hrn Hinj]]]].
  rewrite Erho in Hpre, Hlt.
  set (L' := map rho M).
  set (col' := fun y => tau g (col (linv rho M y))).
  assert (HL'n : forall x, In x L' -> x < n).
  { intros x Hx. unfold L' in Hx. apply in_map_iff in Hx as [z [<- Hz]]. apply Hrn. exact Hz. }
  assert (HlenL' : length L' = N) by (unfold L'; rewrite length_map; exact HlenM).
  assert (Hplane : plane_n n col').
  { apply (IH L' col').
    - exact HlenL'.
    - exact HL'n.
    - exact Hcan.
    - apply rank_lexlt.
      + lia.
      + exact HL'n.
      + exact HLn.
      + exists j. split; [lia|]. split; [exact Hpre|exact Hlt].
    - apply (valid_of_sqv D Hgeo). apply (sqv_ext D (fun i j => tau g (sq_of D col L
          (fst (symf D (fst (fst g)) (snd (fst g)) (snd g) (i, j))) (snd (symf D (fst (fst g)) (snd (fst g)) (snd g) (i, j)))))).
      + intros i j0 Hi Hj. unfold sq_of, col'. destruct (geo_pos D Hgeo i j0 Hi Hj) as [Hp Hc].
        unfold L'. rewrite (nth_map_lt rho M) by lia. rewrite linv_spec; [| |exact Hinj].
        * rewrite HM by lia. unfold im. rewrite nth_image by exact Hp. rewrite Hc. rewrite <- surjective_pairing. reflexivity.
        * apply nth_In. lia.
      + apply sqv_sym. apply sqv_of_valid; [exact Hgeo|exact Hval]. }
  apply (plane_tau n col g). apply (plane_relabel n (fun y => tau g (col y)) (linv rho M)); [|exact Hplane].
  intros y Hy. apply linv_lt; [lia|exact HMn].
Qed.

(** *** Repeat skips *)

Lemma repeat_skip_plane : forall pos k lm H V nu inv pre' lm' H' V' nu' inv',
  pos < N -> NodeInv pos (firstn pos L) k lm H V -> perm_ok n k nu inv = true ->
  NodeInv pos pre' k lm' H' V' -> perm_ok n k nu' inv' = true -> lexlt pre' (firstn pos L) ->
  map (fun l => nth l nu' 0) (map (lab lm') (map pk (frontier D pos))) =
    map (fun l => nth l nu 0) (map (lab lm) (map pk (frontier D pos))) ->
  rrename n inv' H' = rrename n inv H -> rrename n inv' V' = rrename n inv V ->
  plane_n n col.
Proof.
  intros pos k lm H V nu inv pre' lm' H' V' nu' inv' Hpos HI Hp HI' Hp' Hlex Efr EH EV.
  rewrite !map_map in Efr.
  destruct (perm_ok_spec _ _ _ _ Hp) as [P1 P2]. destruct (perm_ok_spec _ _ _ _ Hp') as [P1' P2'].
  destruct (perm_ok_below _ _ _ _ Hp) as [B1 B2]. destruct (perm_ok_below _ _ _ _ Hp') as [B1' B2'].
  set (pi := fun l => nth (nth l nu 0) inv' 0).
  set (sg := fun y => nth (nth y nu' 0) inv 0).
  set (L'' := pre' ++ map pi (skipn pos L)).
  set (col'' := fun y => col (sg y)).
  pose proof (ni_len _ _ _ _ _ _ HI') as Hlen'.
  assert (HlenL'' : length L'' = N) by (unfold L''; rewrite length_app, length_map, length_skipn; lia).
  assert (Hpre_lt : forall p, p < pos -> nth p pre' 0 < n) by (intros; apply (ni_lt _ _ _ _ _ _ HI'); apply nth_In; lia).
  assert (Hlo : forall p, p < pos -> nth p L'' 0 = nth p pre' 0) by (intros; unfold L''; apply app_nth1; lia).
  assert (Hhi : forall p, pos <= p -> p < N -> nth p L'' 0 = pi (nth p L 0)).
  { intros p Hp1 Hp2. unfold L''. rewrite app_nth2 by lia. rewrite Hlen'.
    rewrite nth_indep with (d' := pi 0) by (rewrite length_map, length_skipn; lia).
    rewrite map_nth, nth_skipn. f_equal. f_equal. lia. }
  assert (Hsg_hi : forall p, pos <= p -> p < N -> sg (nth p L'' 0) = nth p L 0).
  { intros p Hp1 Hp2. rewrite Hhi by lia. unfold sg, pi. pose proof (Lnth_lt p) as Hl.
    destruct (P1 _ Hl) as [A1 [A2 _]]. destruct (P2' _ A1) as [C1 [C2 _]]. rewrite C2. exact A2. }
  assert (Hsg_fr : forall p, In p (frontier D pos) -> sg (nth p L'' 0) = nth p L 0).
  { intros p Hp1. assert (Hpp : p < pos).
    { apply (frontier_lt D pos p Hp1). }
    rewrite Hlo by exact Hpp. unfold sg.
    pose proof (map_eq_in _ _ _ p Efr Hp1) as E. cbv beta in E.
    rewrite (ni_lab _ _ _ _ _ _ HI') in E by exact Hpp. rewrite (ni_lab _ _ _ _ _ _ HI) in E by exact Hpp.
    rewrite nth_firstn_lt in E by exact Hpp. rewrite E.
    destruct (P1 _ (Lnth_lt p)) as [_ [A2 _]]. exact A2. }
  assert (HsL : sat right left col H /\ sat bottom top col V).
  { apply (ni_sound _ _ _ _ _ _ HI). apply pvalid_L. lia. }
  assert (Hval'' : valid D col'' L'').
  { intros p q Hp1 Hq1. unfold col''.
    assert (Gen : forall x, x < N -> (pos <= x \/ In x (frontier D pos)) -> sg (nth x L'' 0) = nth x L 0).
    { intros x Hx [H0|H0]; [apply Hsg_hi; lia|apply Hsg_fr; exact H0]. }
    destruct (Nat.lt_ge_cases p pos) as [Hpl|Hpl]; destruct (Nat.lt_ge_cases q pos) as [Hql|Hql].
    - rewrite !Hlo by assumption. split; intros E.
      + pose proof ((ni_cH _ _ _ _ _ _ HI') p q Hpl Hql E) as R'.
        assert (R : rget H (sg (nth p pre' 0)) (sg (nth q pre' 0)) = true).
        { unfold sg. rewrite <- (rget_rrename n inv H) by (apply P1'; apply Hpre_lt; assumption).
          rewrite <- EH. rewrite (rget_rrename n inv' H') by (apply P1'; apply Hpre_lt; assumption).
          destruct (P1' _ (Hpre_lt p Hpl)) as [_ [A2 _]]. destruct (P1' _ (Hpre_lt q Hql)) as [_ [A2' _]].
          rewrite A2, A2'. exact R'. }
        apply (proj1 HsL). exact R.
      + pose proof ((ni_cV _ _ _ _ _ _ HI') p q Hpl Hql E) as R'.
        assert (R : rget V (sg (nth p pre' 0)) (sg (nth q pre' 0)) = true).
        { unfold sg. rewrite <- (rget_rrename n inv V) by (apply P1'; apply Hpre_lt; assumption).
          rewrite <- EV. rewrite (rget_rrename n inv' V') by (apply P1'; apply Hpre_lt; assumption).
          destruct (P1' _ (Hpre_lt p Hpl)) as [_ [A2 _]]. destruct (P1' _ (Hpre_lt q Hql)) as [_ [A2' _]].
          rewrite A2, A2'. exact R'. }
        apply (proj2 HsL). exact R.
    - split; intros E.
      + assert (Fp : In p (frontier D pos)) by (apply (frontier_in D Hgeo pos p q); try lia; unfold adj; rewrite E; reflexivity).
        rewrite (Gen p Hp1 (or_intror Fp)), (Gen q Hq1 (or_introl Hql)). apply (Hval p q Hp1 Hq1). exact E.
      + assert (Fp : In p (frontier D pos)) by (apply (frontier_in D Hgeo pos p q); try lia; unfold adj; rewrite E, orb_true_r; reflexivity).
        rewrite (Gen p Hp1 (or_intror Fp)), (Gen q Hq1 (or_introl Hql)). apply (Hval p q Hp1 Hq1). exact E.
    - split; intros E.
      + assert (Fq : In q (frontier D pos)) by (apply (frontier_in D Hgeo pos q p); try lia; unfold adj; rewrite E, orb_true_r; reflexivity).
        rewrite (Gen p Hp1 (or_introl Hpl)), (Gen q Hq1 (or_intror Fq)). apply (Hval p q Hp1 Hq1). exact E.
      + assert (Fq : In q (frontier D pos)) by (apply (frontier_in D Hgeo pos q p); try lia; unfold adj; rewrite E, orb_true_r; reflexivity).
        rewrite (Gen p Hp1 (or_introl Hpl)), (Gen q Hq1 (or_intror Fq)). apply (Hval p q Hp1 Hq1). exact E.
    - rewrite !Hsg_hi by lia. apply Hval; lia. }
  assert (HL''n : forall x, In x L'' -> x < n).
  { intros x Hx. unfold L'' in Hx. apply in_app_or in Hx as [Hx|Hx]; [apply (ni_lt _ _ _ _ _ _ HI'); exact Hx|].
    apply in_map_iff in Hx as [y [<- Hy]]. unfold pi.
    assert (Hyn : y < n) by (apply HLn; apply (in_skipn_in _ _ _ Hy)).
    destruct (P1 _ Hyn) as [A1 _]. apply (P2' _ A1). }
  assert (Hcan'' : canon 0 L'').
  { unfold L''. apply canon_app. split; [exact (ni_canon _ _ _ _ _ _ HI')|].
    rewrite (ni_k _ _ _ _ _ _ HI').
    rewrite <- (firstn_skipn pos L) in HLc. apply canon_app in HLc as [_ HLc2].
    rewrite (ni_k _ _ _ _ _ _ HI) in HLc2.
    apply (canon_map_perm pi k n (skipn pos L) k); [| | |lia|exact HLc2].
    - intros x Hxk Hxn. unfold pi. apply (B2' _ (B1 x Hxk Hxn)). apply P1. exact Hxn.
    - intros x Hkx Hxn. unfold pi. destruct (P1 x Hxn) as [_ [_ A3]]. rewrite (A3 Hkx).
      destruct (P2' x Hxn) as [_ [_ C3]]. apply C3. exact Hkx.
    - intros x Hx. apply HLn. apply (in_skipn_in _ _ _ Hx). }
  assert (Hlex'' : lexlt L'' L).
  { destruct Hlex as [i [Hi [Hpre Hlt]]]. exists i. rewrite Hlen' in Hi. split; [lia|]. split.
    - unfold L''. rewrite firstn_app. replace (i - length pre') with 0 by lia. simpl. rewrite app_nil_r.
      rewrite Hpre. rewrite firstn_firstn. f_equal. lia.
    - rewrite Hlo by lia. rewrite nth_firstn_lt in Hlt by lia. exact Hlt. }
  assert (Hplane : plane_n n col'').
  { apply (IH L'' col'' HlenL'' HL''n Hcan''); [|exact Hval''].
    apply rank_lexlt; [lia|exact HL''n|exact HLn|exact Hlex'']. }
  apply (plane_relabel n col sg); [|exact Hplane].
  intros y Hy. unfold sg. destruct (P1' y Hy) as [A1 _]. apply (P2 _ A1).
Qed.

(** *** The path lemma *)


Lemma tiles_lab_L : tiles_lab col.
Proof.
  exists (fun r c => nth (pos_of D (r, c)) L 0). split; [|split].
  - intros r c _ _. apply Lnth_lt.
  - intros r c Hr Hc. apply (proj1 (sqv_of_valid D Hgeo col L Hval)); assumption.
  - intros r c Hr Hc. apply (proj2 (sqv_of_valid D Hgeo col L Hval)); assumption.
Qed.

Lemma leaf_plane : forall pos k lm H V, NodeInv pos (firstn pos L) k lm H V -> Settled H V -> plane_n n col.
Proof.
  intros pos k lm H V HI HS. destruct (ni_sound _ _ _ _ _ _ HI col (pvalid_L pos (ni_pos _ _ _ _ _ _ HI))) as [S1 S2].
  apply (HS col S1 S2 tiles_lab_L).
Qed.

Lemma lexlt_child : forall pos t l, pos < N -> t < nth pos L 0 ->
  firstn (S pos) l = firstn pos L ++ [t] -> S pos <= length l -> lexlt l (firstn (length l) L).
Proof.
  intros pos t l Hpos Ht E1 E2. exists pos. split; [lia|]. split.
  - rewrite firstn_firstn, Nat.min_l by lia.
    apply (firstn_prefix l (firstn pos L) t pos E1). rewrite length_firstn. lia.
  - rewrite nth_firstn_lt by lia.
    assert (Hlp : nth pos l 0 = t).
    { rewrite <- (nth_firstn_lt l pos (S pos)) by lia. rewrite E1. rewrite app_nth2 by (rewrite length_firstn; lia).
      rewrite length_firstn, Nat.min_l, Nat.sub_diag by lia. reflexivity. }
    rewrite Hlp. exact Ht.
Qed.

Lemma SeenInv_mono : forall pos m, SeenInv pos m -> SeenInv (S pos) m.
Proof.
  intros pos m HS x Hx. revert x Hx. intros x Hx. generalize (HS x Hx). apply Stored_weaken.
  intros l [A|[A B]]; [left; exact A|right; split; [exact A|lia]].
Qed.

Lemma loop_path : forall (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) pos k lm H V ts s s2,
  NodeInv pos (firstn pos L) k lm H V -> pos < N ->
  (exists j0, ts = seq j0 (length ts) /\ j0 <= nth pos L 0 /\ nth pos L 0 < j0 + length ts) ->
  (forall t, In t ts -> t <= k /\ t < n) ->
  ClosedInv (w_closed s) -> SeenInv (S pos) (w_seen s) ->
  (forall sm t s s', t <= k -> t < n -> w sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (firstn pos L ++ [t]) s s') ->
  (forall sm s s', ClosedInv (w_closed s) -> SeenInv (S pos) (w_seen s) ->
     w sm (if Nat.eqb (nth pos L 0) k then S k else k) (PM.add (pk pos) (nth pos L 0) lm)
       (merges H lm (nth pos L 0) (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm (nth pos L 0) (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     plane_n n col \/ Deferred (w_rec s')) ->
  loop_children w (mk_entry D P pos) k lm H V ts s = Some s2 -> plane_n n col \/ Deferred (w_rec s2).
Proof.
  intros w pos k lm H V ts. induction ts as [|t ts IHt]; intros s s2 HI Hpos [j0 [Ets [Hj0 Hj1]]] Hts HC HS Hoff Hon E.
  - simpl in Hj1. lia.
  - cbn [loop_children] in E. destruct (w _ _ _ _ _ s) as [s'|] eqn:Ew; [|discriminate].
    simpl in Ets. inversion Ets as [[Et Ets']].
    destruct (Hts t (or_introl eq_refl)) as [Htk Htn].
    destruct (Nat.eq_dec t (nth pos L 0)) as [Heq|Hne].
    + rewrite Heq in Ew. destruct (Hon _ s s' HC HS Ew) as [Hp|Hd]; [left; exact Hp|right].
      destruct (loop_frame w pos (firstn pos L) k lm H V ts s' s2 HI Hpos (fun t0 H0 => Hts t0 (or_intror H0))
                  Hoff E) as [_ [[X EX] _]].
      rewrite EX. apply Deferred_app. exact Hd.
    + destruct (Hoff _ t s s' Htk Htn Ew) as [F1 [_ F3]].
      apply (IHt s' s2 HI Hpos); [| |apply F1; exact HC| |exact Hoff|exact Hon|exact E].
      * exists (S j0). rewrite Ets' at 1. split; [reflexivity|]. simpl in Hj1. lia.
      * intros t0 H0. apply Hts. right. exact H0.
      * intros x Hx. destruct (F3 x Hx) as [H1|H1]; [apply HS; exact H1|].
        revert H1. apply Stored_weaken. intros l [E1 E2]. left. apply (lexlt_child pos t l Hpos); [lia|exact E1|exact E2].
Qed.

Lemma pre_labels : forall pos k lm H V, NodeInv pos (firstn pos L) k lm H V -> P <= pos ->
  map (lab lm) (map pk (seq 0 P)) = firstn P L.
Proof.
  intros pos k lm H V HI HP. rewrite map_map.
  assert (Hlen : P <= length L) by (pose proof (ni_pos _ _ _ _ _ _ HI); lia).
  apply (nth_ext _ _ 0 0); [rewrite length_map, length_seq, length_firstn; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (nth_map_seq (fun x => lab lm (pk x))) by exact Hi.
  rewrite (ni_lab _ _ _ _ _ _ HI) by lia. rewrite !nth_firstn_lt by lia. reflexivity.
Qed.

Lemma node_path : forall (w : bool -> nat -> PM.t nat -> rel -> rel -> wst -> option wst) pos same k lm H V s s',
  NodeInv pos (firstn pos L) k lm H V -> ClosedInv (w_closed s) -> SeenInv pos (w_seen s) ->
  (forall sm t s s', t <= k -> t < n -> w sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (firstn pos L ++ [t]) s s') ->
  (forall sm s s', ClosedInv (w_closed s) -> SeenInv (S pos) (w_seen s) ->
     w sm (if Nat.eqb (nth pos L 0) k then S k else k) (PM.add (pk pos) (nth pos L 0) lm)
       (merges H lm (nth pos L 0) (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm (nth pos L 0) (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     plane_n n col \/ Deferred (w_rec s')) ->
  nodeb w (mk_entry D P pos) same k lm H V s = Some s' -> plane_n n col \/ Deferred (w_rec s').
Proof.
  intros w pos same k lm H V s s' HI HC HS Hoff Hon E. unfold node_body in E.
  destruct (nodea (mk_entry D P pos) same H V s) as [[ans s6]|] eqn:Ea; [|discriminate].
  destruct (node_answer_pres _ _ _ _ _ _ _ Ea) as [A6 [B6 C6]].
  assert (HC6 : ClosedInv (w_closed s6)) by (apply C6; exact HC).
  destruct (negb (PrimInt63.eqb ans 0)).
  { destruct (settled_ok n tor s6 ans H V) eqn:Es; [|discriminate]. left.
    apply (leaf_plane pos k lm H V HI). apply (settled_ok_sound _ _ _ _ HC6 Es). }
  destruct (e_full (mk_entry D P pos)) eqn:Efull; [discriminate|].
  pose proof (full_lt pos (ni_pos _ _ _ _ _ _ HI) Efull) as Hpos.
  destruct (rst_of n (mk_entry D P pos) k lm H V) as [r|] eqn:Er; [|discriminate].
  destruct (rst_of_spec _ _ _ _ _ _ _ Er) as [nu [inv [Hp Hr]]].
  cbv zeta in E. generalize dependent E. generalize (enc n r) as xx. intros xx.
  generalize (skey_hash xx) as hh. intros hh E.
  destruct (seen_find n (w_seen s6) hh xx r) eqn:Ef; try discriminate.
  - left. destruct (seen_hit _ _ _ _ _ Ef) as [y [Hy Ey]]. rewrite A6 in Hy.
    destruct (HS y Hy) as [pos' [pre' [k' [lm' [H' [V' [nu' [inv' [HI' [Hpos' [Hp' [Ed Hlex]]]]]]]]]]]].
    rewrite Ed, Hr in Ey. cbn in Ey. injection Ey as E1 E2 E3 E4 E5.
    apply pk_inj in E1. subst pos' k'.
    rewrite (ni_len _ _ _ _ _ _ HI') in Hlex. destruct Hlex as [Hlex|[_ Hlt]]; [|lia].
    apply (repeat_skip_plane pos k lm H V nu inv pre' lm' H' V' nu' inv'); auto.
  - destruct (mark_step s6) as [ins s7] eqn:Em.
    destruct (mark_step_same _ _ _ Em) as [A7 [B7 C7]].
    assert (HC7 : ClosedInv (w_closed s7)) by (rewrite C7; exact HC6).
    assert (HLpos : nth pos L 0 <= k /\ nth pos L 0 < n).
    { split; [|apply Lnth_lt].
      pose proof HLc as HLc'. rewrite <- (firstn_skipn pos L) in HLc'. apply canon_app in HLc' as [_ HLc2].
      rewrite (ni_k _ _ _ _ _ _ HI) in HLc2.
      rewrite <- (firstn_skipn pos L) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
      rewrite length_firstn, Nat.min_l by lia. rewrite Nat.sub_diag.
      destruct (skipn pos L) eqn:Esk; [pose proof (length_skipn pos L); rewrite Esk in H0; simpl in H0; lia|].
      simpl in HLc2. simpl. tauto. }
    destruct ins.
    + destruct (rst_eqb (dec n xx) r) eqn:Ed; [|discriminate].
      pose proof (stored_here_eq pos (firstn pos L) k lm H V r HI Hpos Er xx Ed) as Hst.
      refine (loop_path w pos k lm H V _ _ s' HI Hpos _ (seq_labels k) _ _ Hoff Hon E).
      * exists 0. rewrite length_seq. split; [reflexivity|]. lia.
      * exact HC7.
      * intros x Hx. cbn [w_seen set_seen] in Hx. destruct (InSeen_add x xx (w_seen s7) hh Hx) as [->|H1].
        -- revert Hst. apply Stored_weaken. intros l ->. right. rewrite length_firstn, Nat.min_l by lia.
           split; [reflexivity|lia].
        -- rewrite A7, A6 in H1. apply (SeenInv_mono pos (w_seen s) HS x H1).
    + refine (loop_path w pos k lm H V _ _ s' HI Hpos _ (seq_labels k) _ _ Hoff Hon E).
      * exists 0. rewrite length_seq. split; [reflexivity|]. lia.
      * exact HC7.
      * intros x Hx. rewrite A7, A6 in Hx. apply (SeenInv_mono pos (w_seen s) HS x Hx).
Qed.

Lemma walk_path : forall fuel pos sm k lm H V s s',
  NodeInv pos (firstn pos L) k lm H V -> ClosedInv (w_closed s) -> SeenInv pos (w_seen s) ->
  walkf fuel (tbl pos) sm k lm H V s = Some s' -> plane_n n col \/ Deferred (w_rec s').
Proof.
  induction fuel as [|fuel IHf]; intros pos sm k lm H V s s' HI HC HS E; [discriminate|].
  pose proof (ni_pos _ _ _ _ _ _ HI) as Hpos.
  rewrite tbl_cons, walk_eq in E by exact Hpos.
  change (e_key (mk_entry D P pos)) with (pk pos) in E.
  destruct (sym_skip (images D) (pk pos) lm) eqn:Esym.
  { left. apply (sym_skip_plane pos lm Hpos); [|exact Esym].
    intros q Hq. rewrite (ni_lab _ _ _ _ _ _ HI) by exact Hq. apply nth_firstn_lt. exact Hq. }
  assert (Hoff : forall sm t s s', t <= k -> t < n -> walkf fuel (tbl (S pos)) sm (if Nat.eqb t k then S k else k) (PM.add (pk pos) t lm)
       (merges H lm t (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm t (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     FrameW (S pos) (firstn pos L ++ [t]) s s').
  { intros sm0 t s0 s0' Htk Htn Ew.
    destruct (Nat.eq_dec pos N) as [Ep|Ep].
    - exfalso. rewrite Ep, Nat.sub_diag in Ew. destruct fuel; discriminate.
    - eapply walk_frame; [exact (ni_child pos (firstn pos L) k lm H V t HI ltac:(lia) Htk Htn)|exact Ew]. }
  assert (Hon : forall sm s s', ClosedInv (w_closed s) -> SeenInv (S pos) (w_seen s) ->
     walkf fuel (tbl (S pos)) sm (if Nat.eqb (nth pos L 0) k then S k else k) (PM.add (pk pos) (nth pos L 0) lm)
       (merges H lm (nth pos L 0) (map pk (left_nb D pos)) (map pk (right_nb D pos)))
       (merges V lm (nth pos L 0) (map pk (up_nb D pos)) (map pk (down_nb D pos))) s = Some s' ->
     plane_n n col \/ Deferred (w_rec s')).
  { intros sm0 s0 s0' HC0 HS0 Ew.
    destruct (Nat.eq_dec pos N) as [Ep|Ep].
    - exfalso. rewrite Ep, Nat.sub_diag in Ew. destruct fuel; discriminate.
    - assert (HLpos : nth pos L 0 <= k /\ nth pos L 0 < n).
      { split; [|apply Lnth_lt].
        pose proof HLc as HLc'. rewrite <- (firstn_skipn pos L) in HLc'. apply canon_app in HLc' as [_ HLc2].
        rewrite (ni_k _ _ _ _ _ _ HI) in HLc2.
        rewrite <- (firstn_skipn pos L) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
        rewrite length_firstn, Nat.min_l by lia. rewrite Nat.sub_diag.
        destruct (skipn pos L) eqn:Esk; [pose proof (length_skipn pos L); rewrite Esk in H0; simpl in H0; lia|].
        simpl in HLc2. simpl. tauto. }
      refine (IHf (S pos) sm0 _ _ _ _ s0 s0' _ HC0 HS0 Ew).
      rewrite (firstn_S_nth L pos) by lia.
      apply (ni_child pos (firstn pos L) k lm H V (nth pos L 0) HI ltac:(lia) (proj1 HLpos) (proj2 HLpos)). }
  change (e_reset (mk_entry D P pos)) with (is_reset P pos) in E.
  change (e_pre (mk_entry D P pos)) with (if is_reset P pos then map pk (seq 0 P) else []) in E.
  destruct (is_reset P pos) eqn:Ers.
  - assert (HPpos : P = pos) by (unfold is_reset in Ers; apply andb_true_iff in Ers as [_ Ers]; apply Nat.eqb_eq in Ers; lia).
    rewrite (pre_labels pos k lm H V HI ltac:(lia)) in E.
    destruct (Nat.eqb _ shard) eqn:Esh.
    + destruct (read_token _) as [tok rd].
      destruct (nodeb (walkf fuel (tbl (S pos))) _ false k lm H V _) as [s1|] eqn:E1; [|discriminate].
      cbn [option_map] in E. injection E as Es. subst s'.
      cbn [w_rec clear]. refine (node_path _ pos false k lm H V _ s1 HI _ _ Hoff Hon E1); [exact HC|].
      intros x Hx. cbn [w_seen clear] in Hx. destruct (InSeen_empty x Hx).
    + injection E as Es. subst s'. right. exists [], (w_rec s). split; [reflexivity|]. exact Esh.
  - apply (node_path _ pos sm k lm H V s s' HI HC HS Hoff Hon E).
Qed.

End Path.

Theorem walk_root : forall s0 s',
  walkf (S (S N)) (table D P) false 0 (PM.empty _) (rempty n) (rempty n) s0 = Some s' ->
  w_seen s0 = PM.empty _ -> ClosedInv (w_closed s0) ->
  forall L col, length L = N -> (forall x, In x L -> x < n) -> canon 0 L -> valid D col L ->
  (forall L' col', length L' = N -> (forall x, In x L' -> x < n) -> canon 0 L' ->
     rank n L' < rank n L -> valid D col' L' -> plane_n n col') ->
  plane_n n col \/ Deferred L (w_rec s').
Proof.
  intros s0 s' E Hs0 HC L col HL HLn HLc Hval IH.
  apply (walk_path L col HL HLn HLc Hval IH (S (S N)) 0 false 0 (PM.empty _) (rempty n) (rempty n) s0 s').
  - simpl. apply ni_root.
  - exact HC.
  - rewrite Hs0. intros x Hx. destruct (InSeen_empty x Hx).
  - rewrite Nat.sub_0_r. exact E.
Qed.


End Sound.
