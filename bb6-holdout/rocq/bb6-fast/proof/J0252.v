From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z252 Cuts.b252 Cuts.z253 Cuts.b253 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
