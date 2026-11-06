From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z101 Cuts.b101 Cuts.z102 Cuts.b102 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
