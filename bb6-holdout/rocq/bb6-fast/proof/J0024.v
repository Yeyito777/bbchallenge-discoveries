From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z24 Cuts.b24 Cuts.z25 Cuts.b25 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
