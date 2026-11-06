From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z13 Cuts.b13 Cuts.z14 Cuts.b14 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
