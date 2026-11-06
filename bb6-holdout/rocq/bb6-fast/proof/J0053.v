From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z53 Cuts.b53 Cuts.z54 Cuts.b54 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
