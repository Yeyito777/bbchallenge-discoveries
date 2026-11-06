From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z221 Cuts.b221 Cuts.z222 Cuts.b222 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
