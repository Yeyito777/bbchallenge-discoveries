From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_halt_at XCuts.z706 XCuts.b706 XCuts.y_end XCuts.a_halt XCuts.nh XCuts.vh = true.
Proof. native_cast_no_check (eq_refl true). Qed.
