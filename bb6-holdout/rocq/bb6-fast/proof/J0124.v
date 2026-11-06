From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z124 Cuts.b124 Cuts.z125 Cuts.b125 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
