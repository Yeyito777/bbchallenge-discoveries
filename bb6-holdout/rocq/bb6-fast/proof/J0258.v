From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z258 Cuts.b258 Cuts.z259 Cuts.b259 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
