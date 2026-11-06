From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z230 Cuts.b230 Cuts.z231 Cuts.b231 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
