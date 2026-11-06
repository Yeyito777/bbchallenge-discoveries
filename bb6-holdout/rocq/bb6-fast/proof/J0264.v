From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z264 Cuts.b264 Cuts.z265 Cuts.b265 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
