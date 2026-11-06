From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z209 Cuts.b209 Cuts.z210 Cuts.b210 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
