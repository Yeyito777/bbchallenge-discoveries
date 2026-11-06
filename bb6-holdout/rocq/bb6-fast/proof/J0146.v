From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z146 Cuts.b146 Cuts.z147 Cuts.b147 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
