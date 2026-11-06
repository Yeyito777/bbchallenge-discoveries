From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z269 Cuts.b269 Cuts.z270 Cuts.b270 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
