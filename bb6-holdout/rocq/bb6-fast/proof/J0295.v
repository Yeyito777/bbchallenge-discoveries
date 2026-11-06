From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z295 Cuts.b295 Cuts.z296 Cuts.b296 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
