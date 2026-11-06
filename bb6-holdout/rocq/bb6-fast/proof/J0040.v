From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z40 Cuts.b40 Cuts.z41 Cuts.b41 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
