From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z137 Cuts.b137 Cuts.z138 Cuts.b138 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
