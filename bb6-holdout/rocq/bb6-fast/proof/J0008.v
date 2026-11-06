From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z8 Cuts.b8 Cuts.z9 Cuts.b9 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
