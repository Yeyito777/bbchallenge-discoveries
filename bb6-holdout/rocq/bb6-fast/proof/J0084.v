From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z84 Cuts.b84 Cuts.z85 Cuts.b85 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
