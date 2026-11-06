From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z303 Cuts.b303 Cuts.z304 Cuts.b304 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
