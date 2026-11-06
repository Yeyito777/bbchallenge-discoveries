From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z136 Cuts.b136 Cuts.z137 Cuts.b137 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
