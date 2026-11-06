From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z158 Cuts.b158 Cuts.z159 Cuts.b159 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
