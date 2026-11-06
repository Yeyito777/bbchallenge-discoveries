From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z242 Cuts.b242 Cuts.z243 Cuts.b243 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
