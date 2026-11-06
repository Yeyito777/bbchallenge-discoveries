From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z59 Cuts.b59 Cuts.z60 Cuts.b60 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
