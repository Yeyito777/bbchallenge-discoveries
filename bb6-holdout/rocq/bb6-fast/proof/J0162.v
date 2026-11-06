From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z162 Cuts.b162 Cuts.z163 Cuts.b163 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
