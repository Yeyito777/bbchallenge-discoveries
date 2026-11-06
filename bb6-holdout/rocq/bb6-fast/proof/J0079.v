From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z79 Cuts.b79 Cuts.z80 Cuts.b80 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
