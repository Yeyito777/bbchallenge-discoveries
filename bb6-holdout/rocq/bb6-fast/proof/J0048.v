From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z48 Cuts.b48 Cuts.z49 Cuts.b49 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
