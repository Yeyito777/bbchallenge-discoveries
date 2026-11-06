From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z184 Cuts.b184 Cuts.z185 Cuts.b185 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
