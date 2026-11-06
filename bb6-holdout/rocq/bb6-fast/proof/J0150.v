From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z150 Cuts.b150 Cuts.z151 Cuts.b151 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
