From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z19 Cuts.b19 Cuts.z20 Cuts.b20 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
