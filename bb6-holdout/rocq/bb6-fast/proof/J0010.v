From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z10 Cuts.b10 Cuts.z11 Cuts.b11 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
