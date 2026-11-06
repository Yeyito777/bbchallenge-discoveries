From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z179 Cuts.b179 Cuts.z180 Cuts.b180 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
