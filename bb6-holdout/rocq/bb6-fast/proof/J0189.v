From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z189 Cuts.b189 Cuts.z190 Cuts.b190 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
