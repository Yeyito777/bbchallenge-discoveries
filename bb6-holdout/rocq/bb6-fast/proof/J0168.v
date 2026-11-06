From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z168 Cuts.b168 Cuts.z169 Cuts.b169 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
