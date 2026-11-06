From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z266 Cuts.b266 Cuts.z267 Cuts.b267 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
