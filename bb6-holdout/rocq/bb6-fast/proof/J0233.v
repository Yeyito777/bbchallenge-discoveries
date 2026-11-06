From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z233 Cuts.b233 Cuts.z234 Cuts.b234 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
