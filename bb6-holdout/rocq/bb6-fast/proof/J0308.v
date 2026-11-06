From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z308 Cuts.b308 Cuts.z309 Cuts.b309 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
