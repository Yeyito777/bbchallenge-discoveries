From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z74 Cuts.b74 Cuts.z75 Cuts.b75 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
