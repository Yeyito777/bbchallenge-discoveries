From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z130 Cuts.b130 Cuts.z131 Cuts.b131 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
