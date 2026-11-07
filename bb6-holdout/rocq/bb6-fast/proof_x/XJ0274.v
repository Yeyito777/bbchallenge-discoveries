From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z274 XCuts.b274 XCuts.z275 XCuts.b275 XCuts.n274 XCuts.v274 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
