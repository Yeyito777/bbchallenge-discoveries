From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z82 Cuts.b82 Cuts.z83 Cuts.b83 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
