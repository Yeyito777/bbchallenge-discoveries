From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z289 Cuts.b289 Cuts.z290 Cuts.b290 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
