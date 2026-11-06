From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z15 Cuts.b15 Cuts.z16 Cuts.b16 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
