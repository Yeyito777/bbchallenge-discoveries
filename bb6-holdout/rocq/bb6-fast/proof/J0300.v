From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z300 Cuts.b300 Cuts.z301 Cuts.b301 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
