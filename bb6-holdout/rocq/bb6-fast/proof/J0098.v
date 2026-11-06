From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z98 Cuts.b98 Cuts.z99 Cuts.b99 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
