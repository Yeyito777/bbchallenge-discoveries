From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z156 Cuts.b156 Cuts.z157 Cuts.b157 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
