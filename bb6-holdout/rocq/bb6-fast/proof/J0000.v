From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z0 Cuts.b0 Cuts.z1 Cuts.b1 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
