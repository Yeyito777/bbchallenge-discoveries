From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z32 Cuts.b32 Cuts.z33 Cuts.b33 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
