From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z170 Cuts.b170 Cuts.z171 Cuts.b171 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
