From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z292 Cuts.b292 Cuts.z293 Cuts.b293 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
