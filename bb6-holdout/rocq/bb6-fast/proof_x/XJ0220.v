From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z220 XCuts.b220 XCuts.z221 XCuts.b221 XCuts.n220 XCuts.v220 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
