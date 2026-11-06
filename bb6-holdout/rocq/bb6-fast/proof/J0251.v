From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z251 Cuts.b251 Cuts.z252 Cuts.b252 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
