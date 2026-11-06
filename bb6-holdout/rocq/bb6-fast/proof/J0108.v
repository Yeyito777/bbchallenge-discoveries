From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z108 Cuts.b108 Cuts.z109 Cuts.b109 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
