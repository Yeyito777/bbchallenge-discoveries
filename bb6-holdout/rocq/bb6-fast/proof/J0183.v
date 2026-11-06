From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z183 Cuts.b183 Cuts.z184 Cuts.b184 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
