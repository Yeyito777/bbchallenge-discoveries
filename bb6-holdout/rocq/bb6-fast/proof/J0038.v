From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z38 Cuts.b38 Cuts.z39 Cuts.b39 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
