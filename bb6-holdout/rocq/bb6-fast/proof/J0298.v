From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z298 Cuts.b298 Cuts.z299 Cuts.b299 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
