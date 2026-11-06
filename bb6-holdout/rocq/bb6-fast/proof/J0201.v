From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z201 Cuts.b201 Cuts.z202 Cuts.b202 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
