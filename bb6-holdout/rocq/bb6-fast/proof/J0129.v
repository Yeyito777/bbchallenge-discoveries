From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z129 Cuts.b129 Cuts.z130 Cuts.b130 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
