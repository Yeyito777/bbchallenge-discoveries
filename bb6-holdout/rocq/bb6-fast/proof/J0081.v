From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z81 Cuts.b81 Cuts.z82 Cuts.b82 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
