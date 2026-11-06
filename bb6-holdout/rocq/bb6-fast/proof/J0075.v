From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z75 Cuts.b75 Cuts.z76 Cuts.b76 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
