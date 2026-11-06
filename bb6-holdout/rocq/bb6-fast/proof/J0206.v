From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z206 Cuts.b206 Cuts.z207 Cuts.b207 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
