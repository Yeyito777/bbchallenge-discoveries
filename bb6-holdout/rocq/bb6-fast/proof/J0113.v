From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z113 Cuts.b113 Cuts.z114 Cuts.b114 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
