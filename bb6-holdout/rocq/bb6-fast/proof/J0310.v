From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z310 Cuts.b310 Cuts.z311 Cuts.b311 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
