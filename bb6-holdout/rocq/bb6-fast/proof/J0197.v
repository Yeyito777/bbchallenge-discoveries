From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z197 Cuts.b197 Cuts.z198 Cuts.b198 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
