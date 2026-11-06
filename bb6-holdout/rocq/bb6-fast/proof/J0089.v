From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z89 Cuts.b89 Cuts.z90 Cuts.b90 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
