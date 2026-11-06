From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z283 Cuts.b283 Cuts.z284 Cuts.b284 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
