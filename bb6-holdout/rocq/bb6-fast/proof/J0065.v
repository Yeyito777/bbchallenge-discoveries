From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z65 Cuts.b65 Cuts.z66 Cuts.b66 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
