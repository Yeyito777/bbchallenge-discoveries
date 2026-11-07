From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z131 XCuts.b131 XCuts.z132 XCuts.b132 XCuts.n131 XCuts.v131 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
