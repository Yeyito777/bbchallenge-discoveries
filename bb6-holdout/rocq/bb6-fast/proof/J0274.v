From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z274 Cuts.b274 Cuts.z275 Cuts.b275 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
