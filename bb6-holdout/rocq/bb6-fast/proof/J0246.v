From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z246 Cuts.b246 Cuts.z247 Cuts.b247 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
