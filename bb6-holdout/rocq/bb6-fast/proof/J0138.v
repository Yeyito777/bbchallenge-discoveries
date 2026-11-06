From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z138 Cuts.b138 Cuts.z139 Cuts.b139 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
