From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z235 Cuts.b235 Cuts.z236 Cuts.b236 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
