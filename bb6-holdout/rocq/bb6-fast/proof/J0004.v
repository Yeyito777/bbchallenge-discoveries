From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z4 Cuts.b4 Cuts.z5 Cuts.b5 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
