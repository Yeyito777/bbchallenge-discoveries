(** The theorems: BB_WT(5) = 6, BB_WT(6) = 8, BB_WT(7) >= 16, BB_WT(8) >= 17. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Geom Wang_Upper Wang_Refute Wang_Checker Wang_Champions.
From WangTiles Require Import Wang_Champions_Data Cert_n5_D7 Cert_n6_D9.

(** ** Certificates *)

Lemma geo_7 : geo_ok 7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma geo_9 : geo_ok 9 = true. Proof. vm_compute. reflexivity. Qed.

(** These two run the checker on the stored certificates (wang/certs/upper/n{5,6}_D{7,9}_ringsym). *)
Lemma cert_n5_D7_ok : check [] cert_n5_D7 = true.
Proof. Time native_cast_no_check (eq_refl true). Time Qed.

Lemma cert_n6_D9_ok : check [] cert_n6_D9 = true.
Proof. Time native_cast_no_check (eq_refl true). Time Qed.

Theorem plane_5 : plane_5_statement.
Proof. intros T HT Hsq. exact (check_plane cert_n5_D7 cert_n5_D7_ok eq_refl eq_refl geo_7 T HT Hsq). Qed.

Theorem plane_6 : plane_6_statement.
Proof. intros T HT Hsq. exact (check_plane cert_n6_D9 cert_n6_D9_ok eq_refl eq_refl geo_9 T HT Hsq). Qed.

(** ** Champions *)

Fixpoint nodupb (T : list tile) : bool :=
  match T with [] => true | t :: T' => negb (existsb (tile_eqb t) T') && nodupb T' end.

Lemma nodupb_spec : forall T, nodupb T = true -> NoDup T.
Proof.
  induction T as [|t T IH]; simpl; intros E; [constructor|].
  apply andb_true_iff in E as [E1 E2]. constructor; [|apply IH; exact E2].
  intros Hin. apply negb_true_iff in E1. rewrite <- not_true_iff_false in E1. apply E1.
  apply existsb_exists. exists t. split; [exact Hin|apply tile_eqb_refl].
Qed.

Lemma champion_set : forall T n d G, length T = n -> nodupb T = true ->
  check_tiling T d G = true -> refutes T (S d) = true -> tile_set T n /\ score T d.
Proof.
  intros T n d G Hn Hd E1 E2. split; [split; [exact Hn|apply nodupb_spec; exact Hd]|].
  apply (champion_score T d G E1 E2).
Qed.

Lemma champ_5 : tile_set wiki_n5_tiles 5 /\ score wiki_n5_tiles 6.
Proof. apply (champion_set _ _ _ wiki_n5_tiling); vm_compute; reflexivity. Qed.

Lemma champ_6 : tile_set wiki_n6_tiles 6 /\ score wiki_n6_tiles 8.
Proof. apply (champion_set _ _ _ wiki_n6_tiling); vm_compute; reflexivity. Qed.

Lemma champ_7 : tile_set n7_tiles 7 /\ score n7_tiles 16.
Proof.
  apply (champion_set _ _ _ n7_tiling); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|].
  Time native_cast_no_check (eq_refl true).
Time Qed.

Lemma champ_8 : tile_set n8_tiles 8 /\ score n8_tiles 17.
Proof.
  apply (champion_set _ _ _ n8_tiling); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|].
  Time native_cast_no_check (eq_refl true).
Time Qed.

(** ** The theorems *)

Theorem BB_WT_5 : BB_WT_5_statement.
Proof.
  split; [exists wiki_n5_tiles; exact champ_5|].
  intros T s [HT _] Hs. pose proof (score_upper T s 7 ltac:(lia) (plane_5 T HT) Hs). lia.
Qed.

Theorem BB_WT_6 : BB_WT_6_statement.
Proof.
  split; [exists wiki_n6_tiles; exact champ_6|].
  intros T s [HT _] Hs. pose proof (score_upper T s 9 ltac:(lia) (plane_6 T HT) Hs). lia.
Qed.

Theorem BB_WT_7_lower : BB_WT_7_lower_statement.
Proof. exists n7_tiles, 16. destruct champ_7 as [A B]. auto. Qed.

Theorem BB_WT_8_lower : BB_WT_8_lower_statement.
Proof. exists n8_tiles, 17. destruct champ_8 as [A B]. auto. Qed.

Print Assumptions BB_WT_5.
Print Assumptions BB_WT_6.
Print Assumptions BB_WT_7_lower.
Print Assumptions BB_WT_8_lower.
Print Assumptions plane_6.
