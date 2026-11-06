From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z123 Cuts.b123 Cuts.z124 Cuts.b124 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
