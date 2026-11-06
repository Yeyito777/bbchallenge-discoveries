From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z148 Cuts.b148 Cuts.z149 Cuts.b149 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
