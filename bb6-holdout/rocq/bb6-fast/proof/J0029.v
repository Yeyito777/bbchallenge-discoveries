From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z29 Cuts.b29 Cuts.z30 Cuts.b30 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
