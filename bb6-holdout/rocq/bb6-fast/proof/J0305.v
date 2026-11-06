From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z305 Cuts.b305 Cuts.z306 Cuts.b306 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
