From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z110 Cuts.b110 Cuts.z111 Cuts.b111 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
