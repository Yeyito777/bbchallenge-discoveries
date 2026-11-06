From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z192 Cuts.b192 Cuts.z193 Cuts.b193 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
