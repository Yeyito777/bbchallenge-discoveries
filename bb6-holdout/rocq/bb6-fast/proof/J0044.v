From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z44 Cuts.b44 Cuts.z45 Cuts.b45 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
