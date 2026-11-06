From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z247 Cuts.b247 Cuts.z248 Cuts.b248 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
