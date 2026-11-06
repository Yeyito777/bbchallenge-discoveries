From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z35 Cuts.b35 Cuts.z36 Cuts.b36 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
