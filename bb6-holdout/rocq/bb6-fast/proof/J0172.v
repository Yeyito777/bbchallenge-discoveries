From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z172 Cuts.b172 Cuts.z173 Cuts.b173 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
