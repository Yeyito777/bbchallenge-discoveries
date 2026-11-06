From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z21 Cuts.b21 Cuts.z22 Cuts.b22 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
