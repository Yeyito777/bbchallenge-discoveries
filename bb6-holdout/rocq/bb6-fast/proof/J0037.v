From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z37 Cuts.b37 Cuts.z38 Cuts.b38 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
