From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z93 Cuts.b93 Cuts.z94 Cuts.b94 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
