From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z55 Cuts.b55 Cuts.z56 Cuts.b56 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
