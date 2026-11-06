From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z256 Cuts.b256 Cuts.z257 Cuts.b257 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
