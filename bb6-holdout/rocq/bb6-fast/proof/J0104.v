From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z104 Cuts.b104 Cuts.z105 Cuts.b105 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
