From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z30 Cuts.b30 Cuts.z31 Cuts.b31 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
