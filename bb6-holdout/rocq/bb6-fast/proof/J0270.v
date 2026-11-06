From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z270 Cuts.b270 Cuts.z271 Cuts.b271 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
