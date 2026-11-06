From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z297 Cuts.b297 Cuts.z298 Cuts.b298 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
