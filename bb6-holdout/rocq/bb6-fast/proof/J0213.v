From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z213 Cuts.b213 Cuts.z214 Cuts.b214 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
