From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z28 Cuts.b28 Cuts.z29 Cuts.b29 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
