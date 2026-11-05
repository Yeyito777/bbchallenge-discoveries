(** The theorem BB_WT(7) = 16: the champion of WangTiles_Theorem.v, and the 64 shards of the
    n = 7, D = 17 certificate (wang/certs/n7), each checked in its own file n7/Check7_sNNN.v. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Geom Wang_Upper Wang_Checker Wang_Champions_Data WangTiles_Theorem.
From WangTiles.n7 Require Import Wang7_Prefixes Cert7_s000 Certs7 Checks7.

Lemma geo_17 : geo_ok 17 = true. Proof. vm_compute. reflexivity. Qed.

(** Every prefix appears once in the list the shards share out. *)
Lemma refs7_nodup : NoDup refs7.
Proof. apply nodup_lists_spec. Time native_cast_no_check (eq_refl true). Time Qed.

Lemma certs7_ok : certs_ok refs7 certs7 7 17 10 64.
Proof.
  split.
  - intros c Hc. split; [apply checks7; exact Hc|].
    apply (proj1 (Forall_forall _ certs7) certs7_params c Hc).
  - intros s Hs. exists (nth s certs7 cert7_s000). split; [apply nth_In; rewrite certs7_length; exact Hs|].
    rewrite <- (map_nth c_shard certs7 cert7_s000 s), certs7_shards. apply seq_nth. exact Hs.
Qed.

Theorem plane_7 : plane_7_statement.
Proof. exact (plane_from_certs refs7 certs7 7 17 10 64 certs7_ok refs7_nodup ltac:(lia) geo_17). Qed.

Theorem BB_WT_7 : BB_WT_7_statement.
Proof.
  split; [exists n7_tiles; exact champ_7|].
  intros T s [HT _] Hs. pose proof (score_upper T s 17 ltac:(lia) (plane_7 T HT) Hs). lia.
Qed.

Print Assumptions BB_WT_7.
Print Assumptions plane_7.
