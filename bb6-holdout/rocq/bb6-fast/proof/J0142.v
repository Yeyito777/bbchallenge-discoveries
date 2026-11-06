From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z142 Cuts.b142 Cuts.z143 Cuts.b143 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
