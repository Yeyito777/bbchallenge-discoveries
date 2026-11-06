From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z260 Cuts.b260 Cuts.z261 Cuts.b261 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
