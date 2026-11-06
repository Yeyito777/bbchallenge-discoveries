From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z71 Cuts.b71 Cuts.z72 Cuts.b72 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
