From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z96 Cuts.b96 Cuts.z97 Cuts.b97 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
