From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z105 Cuts.b105 Cuts.z106 Cuts.b106 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
