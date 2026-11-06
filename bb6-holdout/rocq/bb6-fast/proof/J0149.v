From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z149 Cuts.b149 Cuts.z150 Cuts.b150 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
