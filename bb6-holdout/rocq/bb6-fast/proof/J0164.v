From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z164 Cuts.b164 Cuts.z165 Cuts.b165 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
