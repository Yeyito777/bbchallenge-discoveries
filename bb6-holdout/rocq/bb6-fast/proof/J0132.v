From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z132 Cuts.b132 Cuts.z133 Cuts.b133 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
