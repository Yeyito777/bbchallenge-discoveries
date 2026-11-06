From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z17 Cuts.b17 Cuts.z18 Cuts.b18 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
