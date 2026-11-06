From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z219 Cuts.b219 Cuts.z220 Cuts.b220 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
