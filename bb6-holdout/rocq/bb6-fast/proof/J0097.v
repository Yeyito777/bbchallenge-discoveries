From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z97 Cuts.b97 Cuts.z98 Cuts.b98 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
