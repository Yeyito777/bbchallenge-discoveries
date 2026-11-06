From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z203 Cuts.b203 Cuts.z204 Cuts.b204 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
