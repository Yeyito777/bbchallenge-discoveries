From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z178 Cuts.b178 Cuts.z179 Cuts.b179 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
