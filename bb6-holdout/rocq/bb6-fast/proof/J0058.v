From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z58 Cuts.b58 Cuts.z59 Cuts.b59 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
