From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z196 Cuts.b196 Cuts.z197 Cuts.b197 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
