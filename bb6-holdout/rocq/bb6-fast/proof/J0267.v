From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z267 Cuts.b267 Cuts.z268 Cuts.b268 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
