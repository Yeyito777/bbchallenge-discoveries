(** Square tilings by labels, plane tilings, symmetries of the square, and tori. *)
From Coq Require Import List Arith Lia Bool ZArith Uint63.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Rel Wang_Checker.

(** ** Labellings *)

(** A plane tiling by labels 0..n-1, where label i stands for the tile [col i]. *)
Definition plane_n (n : nat) (col : nat -> tile) : Prop :=
  exists P : Z -> Z -> nat,
    (forall i j, P i j < n) /\
    (forall i j, right (col (P i j)) = left (col (P i (j + 1)%Z))) /\
    (forall i j, bottom (col (P i j)) = top (col (P (i + 1)%Z j))).

(** Square validity of a tile function on the DxD square. *)
Definition sqv (D : nat) (F : nat -> nat -> tile) : Prop :=
  (forall i j, i < D -> S j < D -> right (F i j) = left (F i (S j))) /\
  (forall i j, S i < D -> j < D -> bottom (F i j) = top (F (S i) j)).

Lemma sqv_ext : forall D F G, (forall i j, i < D -> j < D -> F i j = G i j) -> sqv D F -> sqv D G.
Proof.
  intros D F G E [H1 H2]. split; intros i j Hi Hj.
  - rewrite <- !E by lia. apply H1; lia.
  - rewrite <- !E by lia. apply H2; lia.
Qed.

Lemma plane_relabel : forall n col (s : nat -> nat),
  (forall y, y < n -> s y < n) -> plane_n n (fun y => col (s y)) -> plane_n n col.
Proof.
  intros n col s Hs [P [HP [H1 H2]]]. exists (fun i j => s (P i j)). split; [|split].
  - intros. apply Hs, HP.
  - intros. apply H1.
  - intros. apply H2.
Qed.

(** ** The three generating symmetries *)

Definition t_sw (t : tile) : tile := mk_tile (left t) (bottom t) (right t) (top t).
Definition t_fr (t : tile) : tile := mk_tile (bottom t) (right t) (top t) (left t).
Definition t_fc (t : tile) : tile := mk_tile (top t) (left t) (bottom t) (right t).

Definition tau (g : bool * bool * bool) (t : tile) : tile :=
  let '(sw, fr, fc) := g in
  (if sw then t_sw else fun x => x) ((if fr then t_fr else fun x => x) ((if fc then t_fc else fun x => x) t)).

Lemma sqv_sw : forall D F, sqv D F -> sqv D (fun i j => t_sw (F j i)).
Proof.
  intros D F [H1 H2]. split; intros i j Hi Hj; simpl.
  - apply H2; lia.
  - apply H1; lia.
Qed.

Lemma sqv_fc : forall D F, sqv D F -> sqv D (fun i j => t_fc (F i (D - 1 - j))).
Proof.
  intros D F [H1 H2]. split; intros i j Hi Hj; simpl.
  - replace (D - 1 - j) with (S (D - 1 - S j)) by lia. symmetry. apply H1; lia.
  - apply H2; lia.
Qed.

Lemma sqv_fr : forall D F, sqv D F -> sqv D (fun i j => t_fr (F (D - 1 - i) j)).
Proof.
  intros D F [H1 H2]. split; intros i j Hi Hj; simpl.
  - apply H1; lia.
  - replace (D - 1 - i) with (S (D - 1 - S i)) by lia. symmetry. apply H2; lia.
Qed.

Lemma sqv_sym : forall D F g, sqv D F ->
  sqv D (fun i j => tau g (F (fst (symf D (fst (fst g)) (snd (fst g)) (snd g) (i, j)))
                              (snd (symf D (fst (fst g)) (snd (fst g)) (snd g) (i, j))))).
Proof.
  intros D F [[sw fr] fc] HF. simpl.
  set (G1 := fun i j => (if fc then t_fc else fun x => x) (F i (if fc then D - 1 - j else j))).
  assert (HG1 : sqv D G1).
  { destruct fc; [apply sqv_fc; exact HF|exact HF]. }
  set (G2 := fun i j => (if fr then t_fr else fun x => x) (G1 (if fr then D - 1 - i else i) j)).
  assert (HG2 : sqv D G2).
  { destruct fr; [apply (sqv_fr D G1 HG1)|exact HG1]. }
  set (G3 := fun i j => (if sw then t_sw else fun x => x) (if sw then G2 j i else G2 i j)).
  assert (HG3 : sqv D G3).
  { destruct sw; [apply (sqv_sw D G2 HG2)|exact HG2]. }
  apply (sqv_ext D G3); [|exact HG3].
  intros i j _ _. unfold G3, G2, G1, symf. destruct sw, fr, fc; reflexivity.
Qed.

Lemma plane_sw : forall n col, plane_n n (fun y => t_sw (col y)) -> plane_n n col.
Proof.
  intros n col [P [HP [H1 H2]]]. exists (fun i j => P j i). split; [|split]; intros i j.
  - apply HP.
  - specialize (H2 j i). simpl in H2. exact H2.
  - specialize (H1 j i). simpl in H1. exact H1.
Qed.

Lemma plane_fc : forall n col, plane_n n (fun y => t_fc (col y)) -> plane_n n col.
Proof.
  intros n col [P [HP [H1 H2]]]. exists (fun i j => P i (- j)%Z). split; [|split]; intros i j.
  - apply HP.
  - specialize (H1 i (- j - 1)%Z). simpl in H1.
    replace (- j - 1 + 1)%Z with (- j)%Z in H1 by lia.
    replace (- (j + 1))%Z with (- j - 1)%Z by lia. symmetry. exact H1.
  - specialize (H2 i (- j)%Z). simpl in H2. exact H2.
Qed.

Lemma plane_fr : forall n col, plane_n n (fun y => t_fr (col y)) -> plane_n n col.
Proof.
  intros n col [P [HP [H1 H2]]]. exists (fun i j => P (- i)%Z j). split; [|split]; intros i j.
  - apply HP.
  - specialize (H1 (- i)%Z j). simpl in H1. exact H1.
  - specialize (H2 (- i - 1)%Z j). simpl in H2.
    replace (- i - 1 + 1)%Z with (- i)%Z in H2 by lia.
    replace (- (i + 1))%Z with (- i - 1)%Z by lia. symmetry. exact H2.
Qed.

Lemma plane_tau : forall n col g, plane_n n (fun y => tau g (col y)) -> plane_n n col.
Proof.
  intros n col [[sw fr] fc] H. simpl in H.
  set (c1 := fun y => (if fc then t_fc else fun x => x) (col y)).
  set (c2 := fun y => (if fr then t_fr else fun x => x) (c1 y)).
  assert (H2 : plane_n n c2).
  { destruct sw; [apply (plane_sw n c2); exact H|exact H]. }
  assert (H1 : plane_n n c1).
  { destruct fr; [apply (plane_fr n c1); exact H2|exact H2]. }
  destruct fc; [apply (plane_fc n col); exact H1|exact H1].
Qed.

Lemma tiles_plane_square : forall T d, tiles_plane T -> tiles_square T d.
Proof.
  intros T d [f [Hin [H1 H2]]].
  exists (fun i j => f (Z.of_nat i) (Z.of_nat j)). split; [|split]; intros i j Hi Hj.
  - apply Hin.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply H1.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply H2.
Qed.

Lemma tiles_square_le : forall T d e, d <= e -> tiles_square T e -> tiles_square T d.
Proof.
  intros T d e Hde [f [Hin [H1 H2]]]. exists f. split; [|split]; intros i j Hi Hj.
  - apply Hin; lia.
  - apply H1; lia.
  - apply H2; lia.
Qed.

(** ** Tori give plane tilings *)

Lemma in_grid_h : forall g r c, r < ga g -> c < gb g ->
  In (gcell g r c, gcell g r ((c + 1) mod gb g)) (grid_h g).
Proof.
  intros g r c Hr Hc. unfold grid_h. apply in_flat_map. exists r. split.
  - apply in_seq. lia.
  - apply in_map_iff. exists c. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma in_grid_v : forall g r c, r < ga g -> c < gb g ->
  In (gcell g r c, if Nat.ltb (r + 1) (ga g) then gcell g (r + 1) c else gcell g 0 ((c + gs g) mod gb g)) (grid_v g).
Proof.
  intros g r c Hr Hc. unfold grid_v. apply in_flat_map. exists r. split.
  - apply in_seq. lia.
  - apply in_map_iff. exists c. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma grid_wf_spec : forall n g, grid_wf n g = true ->
  1 <= ga g /\ 1 <= gb g /\ gs g < gb g /\ length (gc g) = ga g * gb g /\ (forall x, In x (gc g) -> x < n).
Proof.
  intros n g E. unfold grid_wf in E. repeat rewrite andb_true_iff in E.
  destruct E as [[[[E1 E2] E3] E4] E5].
  apply Nat.leb_le in E1. apply Nat.leb_le in E2. apply Nat.ltb_lt in E3. apply Nat.eqb_eq in E4.
  rewrite forallb_forall in E5. repeat split; auto.
  intros x Hx. apply Nat.ltb_lt. apply E5. exact Hx.
Qed.

Lemma gcell_lt : forall n g r c, grid_wf n g = true -> r < ga g -> c < gb g -> gcell g r c < n.
Proof.
  intros n g r c E Hr Hc. destruct (grid_wf_spec n g E) as [_ [_ [_ [Hl Hx]]]].
  apply Hx. unfold gcell. apply nth_In. rewrite Hl. nia.
Qed.

Definition tP (g : grid) (i j : Z) : nat :=
  let A := Z.of_nat (ga g) in let B := Z.of_nat (gb g) in let Sh := Z.of_nat (gs g) in
  gcell g (Z.to_nat (i mod A)) (Z.to_nat ((j + Sh * (i / A)) mod B)).

Lemma mod_succ_nat : forall (x : Z) (b : nat), (0 < Z.of_nat b)%Z ->
  Z.to_nat ((x + 1) mod Z.of_nat b) = (Z.to_nat (x mod Z.of_nat b) + 1) mod b.
Proof.
  intros x b Hb. apply Nat2Z.inj. rewrite Nat2Z.inj_mod, Z2Nat.id by (apply Z.mod_pos_bound; exact Hb).
  rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.mod_pos_bound; exact Hb). simpl.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma mod_add_nat : forall (x : Z) (b s : nat), (0 < Z.of_nat b)%Z ->
  Z.to_nat ((x + Z.of_nat s) mod Z.of_nat b) = (Z.to_nat (x mod Z.of_nat b) + s) mod b.
Proof.
  intros x b s Hb. apply Nat2Z.inj. rewrite Nat2Z.inj_mod, Z2Nat.id by (apply Z.mod_pos_bound; exact Hb).
  rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.mod_pos_bound; exact Hb).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma torus_plane : forall n col g, grid_wf n g = true ->
  (forall p, In p (grid_h g) -> right (col (fst p)) = left (col (snd p))) ->
  (forall p, In p (grid_v g) -> bottom (col (fst p)) = top (col (snd p))) ->
  plane_n n col.
Proof.
  intros n col g Hwf Hh Hv.
  destruct (grid_wf_spec n g Hwf) as [Ha [Hb [Hs _]]].
  set (A := Z.of_nat (ga g)). set (B := Z.of_nat (gb g)). set (Sh := Z.of_nat (gs g)).
  assert (HA : (0 < A)%Z) by (unfold A; lia).
  assert (HB : (0 < B)%Z) by (unfold B; lia).
  exists (tP g). split; [|split].
  - intros i j. unfold tP. fold A B Sh. apply (gcell_lt n); [exact Hwf| |].
    + pose proof (Z.mod_pos_bound i A HA). unfold A in *. lia.
    + pose proof (Z.mod_pos_bound (j + Sh * (i / A)) B HB). unfold B in *. lia.
  - intros i j. unfold tP. fold A B Sh.
    pose proof (Z.mod_pos_bound i A HA) as Hr.
    pose proof (Z.mod_pos_bound (j + Sh * (i / A)) B HB) as Hc.
    replace (j + 1 + Sh * (i / A))%Z with ((j + Sh * (i / A)) + 1)%Z by lia.
    unfold B. rewrite mod_succ_nat by exact HB. fold B.
    apply (Hh (gcell g (Z.to_nat (i mod A)) (Z.to_nat ((j + Sh * (i / A)) mod B)),
               gcell g (Z.to_nat (i mod A)) ((Z.to_nat ((j + Sh * (i / A)) mod B) + 1) mod gb g))).
    apply in_grid_h; unfold A, B in *; lia.
  - intros i j. unfold tP. fold A B Sh.
    pose proof (Z.mod_pos_bound i A HA) as Hr.
    pose proof (Z.div_mod i A ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (j + Sh * (i / A)) B HB) as Hc.
    set (r := Z.to_nat (i mod A)).
    assert (Hr' : Z.of_nat r = (i mod A)%Z) by (unfold r; rewrite Z2Nat.id; lia).
    set (c := Z.to_nat ((j + Sh * (i / A)) mod B)).
    assert (Hc' : Z.of_nat c = ((j + Sh * (i / A)) mod B)%Z) by (unfold c; rewrite Z2Nat.id; lia).
    assert (Hrn : r < ga g) by (unfold A in *; lia).
    assert (Hcn : c < gb g) by (unfold B in *; lia).
    pose proof (in_grid_v g r c Hrn Hcn) as Hin.
    destruct (Nat.ltb (r + 1) (ga g)) eqn:Elt.
    + apply Nat.ltb_lt in Elt.
      assert (Ediv : ((i + 1) / A = i / A)%Z).
      { symmetry. apply Z.div_unique with (r := (i mod A + 1)%Z); [left; unfold A in *; lia|lia]. }
      assert (Emod : ((i + 1) mod A = i mod A + 1)%Z).
      { symmetry. apply Z.mod_unique with (q := (i / A)%Z); [left; unfold A in *; lia|lia]. }
      rewrite Ediv, Emod. fold c.
      replace (Z.to_nat (i mod A + 1)) with (r + 1) by lia.
      apply (Hv _ Hin).
    + apply Nat.ltb_ge in Elt.
      assert (Er : (i mod A = A - 1)%Z) by (unfold A in *; lia).
      assert (Ediv : ((i + 1) / A = i / A + 1)%Z).
      { symmetry. apply Z.div_unique with (r := 0%Z); [left; lia|lia]. }
      assert (Emod : ((i + 1) mod A = 0)%Z).
      { symmetry. apply Z.mod_unique with (q := (i / A + 1)%Z); [left; lia|lia]. }
      rewrite Ediv, Emod.
      replace (j + Sh * (i / A + 1))%Z with ((j + Sh * (i / A)) + Sh)%Z by lia.
      unfold B, Sh. rewrite mod_add_nat by exact HB. fold B Sh. fold c.
      simpl Z.to_nat. apply (Hv _ Hin).
Qed.

Lemma torus_ok_plane : forall n (tor : PArray.array (option (ctorus n))) ans H V col,
  torus_ok tor ans H V = true -> sat right left col H -> sat bottom top col V -> plane_n n col.
Proof.
  intros n tor ans H V col E HH HV. unfold torus_ok in E.
  destruct (PrimInt63.ltb ans 2%uint63); [discriminate|].
  destruct (PArray.get tor (PrimInt63.sub ans 2%uint63)) as [t|]; [|discriminate].
  apply andb_true_iff in E as [E1 E2].
  destruct (t_ok n t) as [g [Hwf [Hh Hv]]].
  apply (torus_plane n col g Hwf).
  - intros p Hp. apply HH. apply (rincl_spec (t_h n t)); [exact E1|]. apply Hh. exact Hp.
  - intros p Hp. apply HV. apply (rincl_spec (t_v n t)); [exact E2|]. apply Hv. exact Hp.
Qed.

(** ** The DxD square in fill order *)

Definition geo_ok (D : nat) : bool :=
  Nat.eqb (length (ring_cells D)) (D * D) &&
  forallb (fun p => Nat.ltb (fst (cell D p)) D && Nat.ltb (snd (cell D p)) D &&
                    Nat.eqb (pos_of D (cell D p)) p) (seq 0 (D * D)) &&
  forallb (fun r => forallb (fun c => Nat.ltb (pos_of D (r, c)) (D * D) &&
                                      pair_eqb (cell D (pos_of D (r, c))) (r, c)) (seq 0 D)) (seq 0 D).

Section Geo.
Variable D : nat.
Hypothesis Hgeo : geo_ok D = true.

Lemma geo_cell : forall p, p < D * D -> fst (cell D p) < D /\ snd (cell D p) < D /\ pos_of D (cell D p) = p.
Proof.
  intros p Hp. unfold geo_ok in Hgeo. repeat rewrite andb_true_iff in Hgeo.
  destruct Hgeo as [[_ H2] _]. rewrite forallb_forall in H2.
  specialize (H2 p ltac:(apply in_seq; lia)). repeat rewrite andb_true_iff in H2.
  destruct H2 as [[A1 A2] A3]. apply Nat.ltb_lt in A1, A2. apply Nat.eqb_eq in A3. auto.
Qed.

Lemma geo_pos : forall r c, r < D -> c < D -> pos_of D (r, c) < D * D /\ cell D (pos_of D (r, c)) = (r, c).
Proof.
  intros r c Hr Hc. unfold geo_ok in Hgeo. repeat rewrite andb_true_iff in Hgeo.
  destruct Hgeo as [_ H3]. rewrite forallb_forall in H3.
  specialize (H3 r ltac:(apply in_seq; lia)). rewrite forallb_forall in H3.
  specialize (H3 c ltac:(apply in_seq; lia)). apply andb_true_iff in H3 as [A1 A2].
  apply Nat.ltb_lt in A1. unfold pair_eqb in A2. apply andb_true_iff in A2 as [B1 B2].
  apply Nat.eqb_eq in B1, B2. split; [exact A1|]. destruct (cell D (pos_of D (r, c))). simpl in *. subst. reflexivity.
Qed.

Lemma hadj_spec : forall p q, hadj D p q = true -> fst (cell D q) = fst (cell D p) /\ snd (cell D q) = S (snd (cell D p)).
Proof.
  intros p q E. unfold hadj in E. destruct (cell D p) as [r1 c1], (cell D q) as [r2 c2].
  apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. simpl. auto.
Qed.

Lemma vadj_spec : forall p q, vadj D p q = true -> snd (cell D q) = snd (cell D p) /\ fst (cell D q) = S (fst (cell D p)).
Proof.
  intros p q E. unfold vadj in E. destruct (cell D p) as [r1 c1], (cell D q) as [r2 c2].
  apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. simpl. auto.
Qed.

Lemma hadj_of : forall r c, r < D -> S c < D -> hadj D (pos_of D (r, c)) (pos_of D (r, S c)) = true.
Proof.
  intros r c Hr Hc. unfold hadj.
  rewrite (proj2 (geo_pos r c Hr ltac:(lia))), (proj2 (geo_pos r (S c) Hr Hc)).
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma vadj_of : forall r c, S r < D -> c < D -> vadj D (pos_of D (r, c)) (pos_of D (S r, c)) = true.
Proof.
  intros r c Hr Hc. unfold vadj.
  rewrite (proj2 (geo_pos r c ltac:(lia) Hc)), (proj2 (geo_pos (S r) c Hr Hc)).
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

(** A full labelling in fill order is valid for [col]. *)
Definition valid (col : nat -> tile) (L : list nat) : Prop :=
  forall p q, p < D * D -> q < D * D ->
    (hadj D p q = true -> right (col (nth p L 0)) = left (col (nth q L 0))) /\
    (vadj D p q = true -> bottom (col (nth p L 0)) = top (col (nth q L 0))).

Definition sq_of (col : nat -> tile) (L : list nat) : nat -> nat -> tile :=
  fun i j => col (nth (pos_of D (i, j)) L 0).

Lemma sqv_of_valid : forall col L, valid col L -> sqv D (sq_of col L).
Proof.
  intros col L HL. split; intros i j Hi Hj; unfold sq_of.
  - apply (HL _ _ (proj1 (geo_pos i j Hi ltac:(lia))) (proj1 (geo_pos i (S j) Hi Hj))).
    apply hadj_of; assumption.
  - apply (HL _ _ (proj1 (geo_pos i j ltac:(lia) Hj)) (proj1 (geo_pos (S i) j Hi Hj))).
    apply vadj_of; assumption.
Qed.

Lemma valid_of_sqv : forall col L, sqv D (sq_of col L) -> valid col L.
Proof.
  intros col L [H1 H2] p q Hp Hq. destruct (geo_cell p Hp) as [Hr1 [Hc1 Hp1]].
  destruct (geo_cell q Hq) as [Hr2 [Hc2 Hq1]]. split; intros E.
  - destruct (hadj_spec p q E) as [E1 E2].
    specialize (H1 (fst (cell D p)) (snd (cell D p)) Hr1 ltac:(lia)). unfold sq_of in H1.
    replace (pos_of D (fst (cell D p), snd (cell D p))) with p in H1
      by (rewrite <- surjective_pairing; symmetry; exact Hp1).
    replace (pos_of D (fst (cell D p), S (snd (cell D p)))) with q in H1
      by (rewrite <- E1, <- E2, <- surjective_pairing; symmetry; exact Hq1).
    exact H1.
  - destruct (vadj_spec p q E) as [E1 E2].
    specialize (H2 (fst (cell D p)) (snd (cell D p)) ltac:(lia) Hc1). unfold sq_of in H2.
    replace (pos_of D (fst (cell D p), snd (cell D p))) with p in H2
      by (rewrite <- surjective_pairing; symmetry; exact Hp1).
    replace (pos_of D (S (fst (cell D p)), snd (cell D p))) with q in H2
      by (rewrite <- E1, <- E2, <- surjective_pairing; symmetry; exact Hq1).
    exact H2.
Qed.

Lemma hadj_irrefl : forall p, hadj D p p = false.
Proof.
  intros p. unfold hadj. destruct (cell D p) as [r c].
  destruct (Nat.eqb (S c) c) eqn:E; [apply Nat.eqb_eq in E; lia|]. apply andb_false_r.
Qed.

Lemma vadj_irrefl : forall p, vadj D p p = false.
Proof.
  intros p. unfold vadj. destruct (cell D p) as [r c].
  destruct (Nat.eqb (S r) r) eqn:E; [apply Nat.eqb_eq in E; lia|]. apply andb_false_r.
Qed.

Lemma symf_range : forall sw fr fc i j, i < D -> j < D ->
  fst (symf D sw fr fc (i, j)) < D /\ snd (symf D sw fr fc (i, j)) < D.
Proof. intros sw fr fc i j Hi Hj. unfold symf. destruct sw, fr, fc; simpl; lia. Qed.


Lemma fold_max_ge : forall l a, a <= fold_left Nat.max l a /\ forall x, In x l -> x <= fold_left Nat.max l a.
Proof.
  induction l as [|y l IH]; intros a; simpl; [split; [lia|intros x []]|].
  destruct (IH (Nat.max a y)) as [A B]. split; [lia|]. intros x [<-|Hx]; [lia|apply B; exact Hx].
Qed.

Lemma frontier_lt : forall pos q, In q (frontier D pos) -> q < pos.
Proof.
  intros pos q Hq. unfold frontier, frontier_of in Hq. apply filter_In in Hq as [Hq _]. apply in_seq in Hq. lia.
Qed.

Lemma frontier_in : forall pos p q, p < pos -> pos <= q -> q < D * D -> adj D p q = true -> In p (frontier D pos).
Proof.
  intros pos p q Hp Hq HqN E. assert (HpN : p < D * D) by lia.
  unfold frontier, frontier_of. apply filter_In. split; [apply in_seq; lia|].
  apply Nat.leb_le. unfold maxl_of. rewrite (nth_indep _ _ ((maxnb_of (ring_cells D) D) 0)) by (rewrite length_map, length_seq; exact HpN).
  rewrite map_nth, seq_nth by exact HpN. simpl. unfold maxnb_of.
  change (nth p (ring_cells D) (0, 0)) with (cell D p).
  destruct (geo_cell p HpN) as [Hr1 [Hc1 _]]. destruct (geo_cell q HqN) as [Hr2 [Hc2 Hq2]].
  assert (Hin : In (cell D q) (nbr_coords D (fst (cell D p)) (snd (cell D p)))).
  { unfold nbr_coords. unfold adj in E.
    destruct (hadj D p q) eqn:E1; [|destruct (hadj D q p) eqn:E2; [|destruct (vadj D p q) eqn:E3; [|destruct (vadj D q p) eqn:E4]]];
      simpl in E; try discriminate.
    - destruct (hadj_spec p q E1) as [A B]. apply in_or_app. left.
      rewrite (proj2 (Nat.ltb_lt _ _)) by lia. left. rewrite (surjective_pairing (cell D q)), A, B. reflexivity.
    - destruct (hadj_spec q p E2) as [A B]. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Nat.ltb_lt 0 _)) by lia. left. rewrite (surjective_pairing (cell D q)), <- A, B.
      f_equal. lia.
    - destruct (vadj_spec p q E3) as [A B]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Nat.ltb_lt _ _)) by lia. left. rewrite (surjective_pairing (cell D q)), A, B. reflexivity.
    - destruct (vadj_spec q p E4) as [A B]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      rewrite (proj2 (Nat.ltb_lt 0 _)) by lia. left. rewrite (surjective_pairing (cell D q)), <- A, B.
      f_equal. lia. }
  destruct (cell D p) as [r c]. simpl in Hin.
  apply (Nat.le_trans _ q); [exact Hq|].
  apply (proj2 (fold_max_ge _ 0)). apply in_map_iff. exists (cell D q). split; [|exact Hin].
  exact Hq2.
Qed.

End Geo.
