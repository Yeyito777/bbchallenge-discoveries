From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z309 Cuts.b309 Cuts.z310 Cuts.b310 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
