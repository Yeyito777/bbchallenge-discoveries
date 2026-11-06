From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z231 Cuts.b231 Cuts.z232 Cuts.b232 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
