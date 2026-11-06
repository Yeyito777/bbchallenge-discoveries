From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z14 Cuts.b14 Cuts.z15 Cuts.b15 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
