From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z12 Cuts.b12 Cuts.z13 Cuts.b13 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
