From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z46 Cuts.b46 Cuts.z47 Cuts.b47 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
