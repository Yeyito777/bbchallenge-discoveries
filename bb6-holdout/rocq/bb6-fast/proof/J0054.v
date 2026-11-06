From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z54 Cuts.b54 Cuts.z55 Cuts.b55 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
