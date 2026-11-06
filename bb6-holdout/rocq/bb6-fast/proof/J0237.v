From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z237 Cuts.b237 Cuts.z238 Cuts.b238 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
