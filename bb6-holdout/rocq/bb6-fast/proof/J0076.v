From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z76 Cuts.b76 Cuts.z77 Cuts.b77 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
