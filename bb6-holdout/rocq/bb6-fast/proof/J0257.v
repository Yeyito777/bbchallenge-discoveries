From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_seg Cuts.z257 Cuts.b257 Cuts.z258 Cuts.b258 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
