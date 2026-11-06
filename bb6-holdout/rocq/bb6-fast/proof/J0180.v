From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z180 Cuts.b180 Cuts.z181 Cuts.b181 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
