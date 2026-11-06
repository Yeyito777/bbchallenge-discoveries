From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z268 Cuts.b268 Cuts.z269 Cuts.b269 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
