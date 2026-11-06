From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z244 Cuts.b244 Cuts.z245 Cuts.b245 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
