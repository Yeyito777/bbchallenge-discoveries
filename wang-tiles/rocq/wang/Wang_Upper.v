(** From a passing certificate to tile sets: every n-tile set that tiles DxD tiles the plane. *)
From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Rel Wang_Refute Wang_Checker Wang_Geom Wang_Canon Wang_Sound.

Definition dflt_tile : tile := mk_tile 0 0 0 0.

Definition tile_eqb (a b : tile) : bool :=
  Nat.eqb (top a) (top b) && Nat.eqb (right a) (right b) && Nat.eqb (bottom a) (bottom b) && Nat.eqb (left a) (left b).

Lemma tile_eqb_eq : forall a b, tile_eqb a b = true -> a = b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] E. unfold tile_eqb in E. simpl in E.
  repeat rewrite andb_true_iff in E. destruct E as [[[E1 E2] E3] E4].
  apply Nat.eqb_eq in E1, E2, E3, E4. subst. reflexivity.
Qed.

Lemma tile_eqb_refl : forall a, tile_eqb a a = true.
Proof. intros [a1 a2 a3 a4]. unfold tile_eqb. simpl. rewrite !Nat.eqb_refl. reflexivity. Qed.

(** The position of a tile in the list. *)
Fixpoint tindex (t : tile) (T : list tile) : nat :=
  match T with [] => 0 | u :: T' => if tile_eqb t u then 0 else S (tindex t T') end.

Lemma tindex_spec : forall t T, In t T -> tindex t T < length T /\ nth (tindex t T) T dflt_tile = t.
Proof.
  intros t. induction T as [|u T IH]; intros Hin; simpl in *; [tauto|].
  destruct (tile_eqb t u) eqn:E.
  - apply tile_eqb_eq in E. subst. split; [lia|reflexivity].
  - destruct Hin as [->|Hin]; [rewrite tile_eqb_refl in E; discriminate|].
    destruct (IH Hin). split; [lia|assumption].
Qed.

Lemma plane_of_plane_n : forall T, plane_n (length T) (fun i => nth i T dflt_tile) -> tiles_plane T.
Proof.
  intros T [P [HP [H1 H2]]]. exists (fun i j => nth (P i j) T dflt_tile). split; [|split].
  - intros i j. apply nth_In. apply HP.
  - exact H1.
  - exact H2.
Qed.

Lemma lists_eqb_eq : forall x y, lists_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y]; simpl; try discriminate; auto.
  intros E. apply andb_true_iff in E as [E1 E2]. apply list_eqb_eq in E1. subst. f_equal. auto.
Qed.

Lemma list_eqb_refl : forall l, list_eqb l l = true.
Proof. induction l; simpl; [reflexivity|rewrite Nat.eqb_refl; exact IHl]. Qed.

Fixpoint nodup_lists (l : list (list nat)) : bool :=
  match l with [] => true | x :: l' => negb (existsb (list_eqb x) l') && nodup_lists l' end.

Lemma nodup_lists_spec : forall l, nodup_lists l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros E; [constructor|].
  apply andb_true_iff in E as [E1 E2]. constructor; [|apply IH; exact E2].
  intros Hin. apply negb_true_iff in E1. rewrite <- not_true_iff_false in E1. apply E1.
  apply existsb_exists. exists x. split; [exact Hin|apply list_eqb_refl].
Qed.

(** A family of certificates: shards 0..S-1 of one tree (one shard when S = 1), each passing
    with the same list of reset prefixes [refs]. *)
Definition certs_ok (refs : list (list nat)) (certs : list cert) (n D P Sh : nat) : Prop :=
  (forall c, In c certs -> check refs c = true /\ c_n c = n /\ c_D c = D /\ c_reset c = P /\ c_shards c = Sh) /\
  (forall s, s < Sh -> exists c, In c certs /\ c_shard c = s).

(** Every valid labelling of the square (labels by first appearance) gives a plane tiling.
    By induction on the labelling read as a number: follow it in shard 0; if shard 0 leaves its
    prefix to shard t, follow it in shard t, which walks that prefix, because both recorded the
    same list of prefixes and a prefix appears in it once. *)
Theorem labels_sound : forall refs certs n D P Sh, certs_ok refs certs n D P Sh -> NoDup refs -> 0 < Sh ->
  geo_ok D = true ->
  forall L col, length L = D * D -> (forall x, In x L -> x < n) -> canon 0 L -> valid D col L -> plane_n n col.
Proof.
  intros refs certs n D P Sh [Hc Hcov] Hnd HS Hgeo L.
  induction L as [L IHL] using (well_founded_induction (well_founded_ltof _ (rank n))).
  intros col HL HLn HLc Hval.
  assert (Path : forall c, In c certs -> plane_n n col \/
            exists i, nth_error refs i = Some (firstn P L) /\ Nat.eqb (S i mod Sh) (c_shard c) = false).
  { intros c Hin. destruct (Hc c Hin) as [Hck [En [ED [EP ES]]]].
    unfold check in Hck. repeat rewrite andb_true_iff in Hck. destruct Hck as [[[Hn _] _] Hrun].
    apply Nat.leb_le in Hn.
    destruct (run c) as [s'|] eqn:Er; [|discriminate]. apply andb_true_iff in Hrun as [_ Href].
    apply lists_eqb_eq in Href.
    unfold run in Er. cbv zeta in Er. rewrite En, ED, EP, ES in Er. rewrite En in Hn.
    destruct (walk_root n D P Sh (c_shard c) Hn Hgeo _ _ _ _ s' Er eq_refl (ClosedInv_empty _ _) L col HL HLn HLc Hval
                (fun L' col' A B C R V => IHL L' R col' A B C V)) as [Hp|[X [rest [Erec Esh]]]].
    - left. exact Hp.
    - right. exists (length rest). split; [|exact Esh].
      rewrite <- Href, Erec, rev_app_distr. simpl. rewrite <- app_assoc. simpl.
      rewrite nth_error_app2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity. }
  destruct (Hcov 0 HS) as [c0 [Hin0 Hs0]].
  destruct (Path c0 Hin0) as [Hp|[i [Hi Hne]]]; [exact Hp|].
  destruct (Hcov (S i mod Sh) (Nat.mod_upper_bound (S i) Sh ltac:(lia))) as [c1 [Hin1 Hs1]].
  destruct (Path c1 Hin1) as [Hp|[j [Hj Hne']]]; [exact Hp|].
  assert (Hij : i = j).
  { apply (proj1 (NoDup_nth_error refs) Hnd); [|congruence].
    apply nth_error_Some. rewrite Hi. discriminate. }
  subst j. rewrite Hs1, Nat.eqb_refl in Hne'. discriminate.
Qed.

(** From labellings to lists of tiles. *)
Theorem plane_from_certs : forall refs certs n D P Sh, certs_ok refs certs n D P Sh -> NoDup refs -> 0 < Sh ->
  geo_ok D = true -> forall T, length T = n -> tiles_square T D -> tiles_plane T.
Proof.
  intros refs certs n D P Sh Hok Hnd HS Hgeo T HT [f [Hin [H1 H2]]].
  set (col := fun i => nth i T dflt_tile).
  set (L0 := map (fun p => tindex (f (fst (cell D p)) (snd (cell D p))) T) (seq 0 (D * D))).
  assert (Hcell : forall p, p < D * D -> In (f (fst (cell D p)) (snd (cell D p))) T).
  { intros p Hp. destruct (geo_cell D Hgeo p Hp) as [A1 [A2 _]]. apply Hin; assumption. }
  assert (HL0 : forall x, In x L0 -> x < n).
  { intros x Hx. unfold L0 in Hx. apply in_map_iff in Hx as [p [<- Hp]]. apply in_seq in Hp.
    rewrite <- HT. apply tindex_spec. apply Hcell. lia. }
  destruct (canon_rename n L0 HL0) as [rho [_ [Hcan [Hrn Hinj]]]].
  set (L := map rho L0).
  set (col' := fun y => col (linv rho L0 y)).
  assert (HlenL0 : length L0 = D * D) by (unfold L0; rewrite length_map, length_seq; reflexivity).
  assert (Hpl : plane_n n col').
  { apply (labels_sound refs certs n D P Sh Hok Hnd HS Hgeo L col').
    - unfold L. rewrite length_map. exact HlenL0.
    - intros x Hx. unfold L in Hx. apply in_map_iff in Hx as [z [<- Hz]]. apply Hrn. exact Hz.
    - exact Hcan.
    - apply (valid_of_sqv D Hgeo). apply (sqv_ext D f).
      + intros i j Hi Hj. unfold sq_of, col', col, L. destruct (geo_pos D Hgeo i j Hi Hj) as [Hp Hc].
        rewrite (nth_map_lt rho L0) by lia. rewrite linv_spec; [| |exact Hinj].
        * unfold L0. rewrite (nth_map_seq (fun p => tindex (f (fst (cell D p)) (snd (cell D p))) T)) by exact Hp.
          rewrite Hc. simpl. symmetry. apply tindex_spec. apply Hin; assumption.
        * apply nth_In. lia.
      + split; [exact H1|exact H2]. }
  apply plane_of_plane_n. rewrite HT.
  apply (plane_relabel n col (linv rho L0)); [|exact Hpl].
  intros y Hy. apply linv_lt; [lia|exact HL0].
Qed.

(** One certificate without resets or shards (n <= 6). *)
Theorem check_plane : forall c, check [] c = true -> c_reset c = 0 -> c_shards c = 1 -> geo_ok (c_D c) = true ->
  forall T, length T = c_n c -> tiles_square T (c_D c) -> tiles_plane T.
Proof.
  intros c Hc HP HS Hgeo. apply (plane_from_certs [] [c] (c_n c) (c_D c) 0 1); [|constructor|lia|exact Hgeo].
  split.
  - intros c' [<-|[]]. auto.
  - intros s Hs. exists c. split; [left; reflexivity|].
    unfold check in Hc. repeat rewrite andb_true_iff in Hc. destruct Hc as [[[_ Hsh] _] _].
    apply Nat.ltb_lt in Hsh. lia.
Qed.

(** From "every n-tile set that tiles DxD tiles the plane" to the upper bound on scores. *)
Lemma score_upper : forall T s D, 1 <= D -> (tiles_square T D -> tiles_plane T) -> score T s -> s < D.
Proof.
  intros T s D HD HP [[Hsq Hmax]|[-> _]].
  - destruct (Nat.lt_ge_cases s D) as [H|H]; [exact H|].
    exfalso. pose proof (HP (tiles_square_le T D s H Hsq)) as Hpl.
    pose proof (Hmax (S s) (tiles_plane_square T (S s) Hpl)). lia.
  - exact HD.
Qed.
