From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z224 Cuts.b224 Cuts.z225 Cuts.b225 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
