From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z211 Cuts.b211 Cuts.z212 Cuts.b212 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
