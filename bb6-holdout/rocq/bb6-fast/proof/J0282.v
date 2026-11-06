From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z282 Cuts.b282 Cuts.z283 Cuts.b283 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
