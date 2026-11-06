From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z166 Cuts.b166 Cuts.z167 Cuts.b167 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
