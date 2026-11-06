From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z39 Cuts.b39 Cuts.z40 Cuts.b40 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
