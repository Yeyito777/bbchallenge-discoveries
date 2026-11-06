From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z185 Cuts.b185 Cuts.z186 Cuts.b186 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
