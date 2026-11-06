From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z107 Cuts.b107 Cuts.z108 Cuts.b108 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
