From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z26 Cuts.b26 Cuts.z27 Cuts.b27 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
