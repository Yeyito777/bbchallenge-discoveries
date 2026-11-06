From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z128 Cuts.b128 Cuts.z129 Cuts.b129 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
