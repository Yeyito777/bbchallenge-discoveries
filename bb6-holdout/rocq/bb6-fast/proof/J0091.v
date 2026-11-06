From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z91 Cuts.b91 Cuts.z92 Cuts.b92 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
