From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z73 Cuts.b73 Cuts.z74 Cuts.b74 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
