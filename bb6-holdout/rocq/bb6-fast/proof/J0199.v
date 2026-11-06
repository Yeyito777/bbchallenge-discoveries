From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z199 Cuts.b199 Cuts.z200 Cuts.b200 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
