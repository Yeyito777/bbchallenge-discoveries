From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z239 Cuts.b239 Cuts.z240 Cuts.b240 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
