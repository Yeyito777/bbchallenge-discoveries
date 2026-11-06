From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z23 Cuts.b23 Cuts.z24 Cuts.b24 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
