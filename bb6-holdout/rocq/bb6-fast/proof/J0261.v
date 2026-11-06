From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z261 Cuts.b261 Cuts.z262 Cuts.b262 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
