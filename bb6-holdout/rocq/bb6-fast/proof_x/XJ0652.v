From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z652 XCuts.b652 XCuts.z653 XCuts.b653 XCuts.n652 XCuts.v652 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
