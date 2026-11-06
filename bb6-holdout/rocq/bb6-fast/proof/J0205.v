From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z205 Cuts.b205 Cuts.z206 Cuts.b206 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
