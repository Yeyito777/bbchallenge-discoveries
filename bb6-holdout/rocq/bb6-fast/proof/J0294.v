From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z294 Cuts.b294 Cuts.z295 Cuts.b295 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
