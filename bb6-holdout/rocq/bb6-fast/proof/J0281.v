From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z281 Cuts.b281 Cuts.z282 Cuts.b282 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
