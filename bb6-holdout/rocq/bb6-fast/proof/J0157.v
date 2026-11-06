From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z157 Cuts.b157 Cuts.z158 Cuts.b158 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
