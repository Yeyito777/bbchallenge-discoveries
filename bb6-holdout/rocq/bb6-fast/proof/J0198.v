From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z198 Cuts.b198 Cuts.z199 Cuts.b199 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
