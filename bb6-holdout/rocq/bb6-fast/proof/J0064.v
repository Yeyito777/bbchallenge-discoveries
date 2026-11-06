From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z64 Cuts.b64 Cuts.z65 Cuts.b65 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
