From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z311 Cuts.b311 Cuts.z312 Cuts.b312 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
