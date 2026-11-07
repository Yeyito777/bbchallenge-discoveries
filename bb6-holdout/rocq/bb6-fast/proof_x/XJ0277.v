From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z277 XCuts.b277 XCuts.z278 XCuts.b278 XCuts.n277 XCuts.v277 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
