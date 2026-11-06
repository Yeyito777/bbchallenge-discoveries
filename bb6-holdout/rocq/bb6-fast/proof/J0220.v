From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z220 Cuts.b220 Cuts.z221 Cuts.b221 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
