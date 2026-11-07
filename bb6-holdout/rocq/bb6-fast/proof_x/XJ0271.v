From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z271 XCuts.b271 XCuts.z272 XCuts.b272 XCuts.n271 XCuts.v271 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
