From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z190 Cuts.b190 Cuts.z191 Cuts.b191 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
