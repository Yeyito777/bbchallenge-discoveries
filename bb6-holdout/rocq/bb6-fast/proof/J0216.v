From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z216 Cuts.b216 Cuts.z217 Cuts.b217 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
