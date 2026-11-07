From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z597 XCuts.b597 XCuts.z598 XCuts.b598 XCuts.n597 XCuts.v597 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
