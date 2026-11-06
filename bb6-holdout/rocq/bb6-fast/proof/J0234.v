From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z234 Cuts.b234 Cuts.z235 Cuts.b235 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
