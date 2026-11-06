From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z116 Cuts.b116 Cuts.z117 Cuts.b117 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
