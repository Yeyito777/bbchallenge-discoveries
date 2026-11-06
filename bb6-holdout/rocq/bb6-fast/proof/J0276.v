From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z276 Cuts.b276 Cuts.z277 Cuts.b277 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
