From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z271 Cuts.b271 Cuts.z272 Cuts.b272 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
