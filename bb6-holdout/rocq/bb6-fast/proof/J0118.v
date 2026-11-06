From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z118 Cuts.b118 Cuts.z119 Cuts.b119 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
