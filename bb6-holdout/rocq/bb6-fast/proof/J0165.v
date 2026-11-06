From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z165 Cuts.b165 Cuts.z166 Cuts.b166 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
