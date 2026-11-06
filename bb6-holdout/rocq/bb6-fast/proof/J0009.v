From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z9 Cuts.b9 Cuts.z10 Cuts.b10 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
