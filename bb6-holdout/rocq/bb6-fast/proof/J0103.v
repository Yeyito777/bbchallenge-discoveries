From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z103 Cuts.b103 Cuts.z104 Cuts.b104 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
