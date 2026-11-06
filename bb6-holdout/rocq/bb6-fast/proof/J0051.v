From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z51 Cuts.b51 Cuts.z52 Cuts.b52 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
