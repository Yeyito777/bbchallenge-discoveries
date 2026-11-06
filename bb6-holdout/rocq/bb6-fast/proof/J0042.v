From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z42 Cuts.b42 Cuts.z43 Cuts.b43 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
