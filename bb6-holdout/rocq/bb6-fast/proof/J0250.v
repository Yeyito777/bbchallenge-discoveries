From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z250 Cuts.b250 Cuts.z251 Cuts.b251 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
