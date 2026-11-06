From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z126 Cuts.b126 Cuts.z127 Cuts.b127 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
