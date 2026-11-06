From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z280 Cuts.b280 Cuts.z281 Cuts.b281 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
