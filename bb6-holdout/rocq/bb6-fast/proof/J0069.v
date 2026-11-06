From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z69 Cuts.b69 Cuts.z70 Cuts.b70 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
