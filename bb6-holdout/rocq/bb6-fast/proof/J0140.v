From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z140 Cuts.b140 Cuts.z141 Cuts.b141 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
