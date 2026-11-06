From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z152 Cuts.b152 Cuts.z153 Cuts.b153 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
