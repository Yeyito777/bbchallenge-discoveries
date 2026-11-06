From Coq Require Import Uint63.
From BF Require Import HTop.
Require Cuts.
Lemma seg : run_halt_at Cuts.z312 Cuts.b312 Cuts.y_end Cuts.a_halt = true.
Proof. native_cast_no_check (eq_refl true). Qed.
