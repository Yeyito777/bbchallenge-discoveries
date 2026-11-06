From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z33 Cuts.b33 Cuts.z34 Cuts.b34 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
