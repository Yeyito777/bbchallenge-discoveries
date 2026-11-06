From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z181 Cuts.b181 Cuts.z182 Cuts.b182 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
