From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z43 Cuts.b43 Cuts.z44 Cuts.b44 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
