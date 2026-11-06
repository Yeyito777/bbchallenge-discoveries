From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z285 Cuts.b285 Cuts.z286 Cuts.b286 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
