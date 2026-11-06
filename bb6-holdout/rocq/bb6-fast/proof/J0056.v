From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z56 Cuts.b56 Cuts.z57 Cuts.b57 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
