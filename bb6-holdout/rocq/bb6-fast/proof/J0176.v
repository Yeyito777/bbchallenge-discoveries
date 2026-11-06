From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z176 Cuts.b176 Cuts.z177 Cuts.b177 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
