From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z194 Cuts.b194 Cuts.z195 Cuts.b195 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
