From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z130 XCuts.b130 XCuts.z131 XCuts.b131 XCuts.n130 XCuts.v130 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
