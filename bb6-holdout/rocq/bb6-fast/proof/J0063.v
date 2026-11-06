From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z63 Cuts.b63 Cuts.z64 Cuts.b64 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
