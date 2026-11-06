From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z279 Cuts.b279 Cuts.z280 Cuts.b280 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
