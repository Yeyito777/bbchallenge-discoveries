From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z135 Cuts.b135 Cuts.z136 Cuts.b136 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
