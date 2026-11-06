From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z265 Cuts.b265 Cuts.z266 Cuts.b266 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
