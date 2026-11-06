From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z155 Cuts.b155 Cuts.z156 Cuts.b156 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
