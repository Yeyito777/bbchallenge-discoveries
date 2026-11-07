From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z272 XCuts.b272 XCuts.z273 XCuts.b273 XCuts.n272 XCuts.v272 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
