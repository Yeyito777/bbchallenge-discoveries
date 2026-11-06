From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z115 Cuts.b115 Cuts.z116 Cuts.b116 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
