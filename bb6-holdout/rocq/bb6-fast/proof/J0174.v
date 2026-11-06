From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z174 Cuts.b174 Cuts.z175 Cuts.b175 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
