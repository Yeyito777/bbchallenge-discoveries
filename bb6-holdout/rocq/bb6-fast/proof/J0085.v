From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z85 Cuts.b85 Cuts.z86 Cuts.b86 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
