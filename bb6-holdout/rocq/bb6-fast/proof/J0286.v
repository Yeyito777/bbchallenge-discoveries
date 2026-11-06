From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z286 Cuts.b286 Cuts.z287 Cuts.b287 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
