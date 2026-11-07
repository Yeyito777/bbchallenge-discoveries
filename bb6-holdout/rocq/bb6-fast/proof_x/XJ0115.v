From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z115 XCuts.b115 XCuts.z116 XCuts.b116 XCuts.n115 XCuts.v115 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
