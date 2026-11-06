From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z187 Cuts.b187 Cuts.z188 Cuts.b188 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
