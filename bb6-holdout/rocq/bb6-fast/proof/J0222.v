From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z222 Cuts.b222 Cuts.z223 Cuts.b223 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
