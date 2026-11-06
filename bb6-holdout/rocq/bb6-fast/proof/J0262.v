From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z262 Cuts.b262 Cuts.z263 Cuts.b263 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
