From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z284 XCuts.b284 XCuts.z285 XCuts.b285 XCuts.n284 XCuts.v284 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
