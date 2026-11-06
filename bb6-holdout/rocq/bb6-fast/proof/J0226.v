From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z226 Cuts.b226 Cuts.z227 Cuts.b227 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
