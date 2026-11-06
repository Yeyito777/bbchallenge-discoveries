From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z229 Cuts.b229 Cuts.z230 Cuts.b230 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
