From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z67 Cuts.b67 Cuts.z68 Cuts.b68 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
