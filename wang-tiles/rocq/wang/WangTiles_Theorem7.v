(** The theorem BB_WT(7) = 16: the champion of WangTiles_Theorem.v, and the jobs of the n = 7,
    D = 17 certificate (made from wang/certs/n7 by tools/make_n7.sh), each checked in its own file
    n7/Check7_jJJJ.v and collected in n7/Jobs7.v. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From WangTiles Require Import WangTiles_Statement Wang_Geom Wang_Upper Wang_Checker Wang_Champions_Data WangTiles_Theorem.
From WangTiles.n7 Require Import Wang7_Prefixes Jobs7.

Lemma geo_17 : geo_ok 17 = true. Proof. vm_compute. reflexivity. Qed.

Theorem plane_7 : plane_7_statement.
Proof.
  exact (plane_from_certs refs7 owners7 certs7 7 17 10 njobs7 certs7_ok refs7_nodup
           ltac:(unfold njobs7; lia) geo_17).
Qed.

Theorem BB_WT_7 : BB_WT_7_statement.
Proof.
  split; [exists n7_tiles; exact champ_7|].
  intros T s [HT _] Hs. pose proof (score_upper T s 17 ltac:(lia) (plane_7 T HT) Hs). lia.
Qed.

Print Assumptions BB_WT_7.
Print Assumptions plane_7.
