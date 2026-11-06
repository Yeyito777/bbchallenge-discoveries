From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z302 Cuts.b302 Cuts.z303 Cuts.b303 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
