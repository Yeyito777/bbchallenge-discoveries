From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z160 Cuts.b160 Cuts.z161 Cuts.b161 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
