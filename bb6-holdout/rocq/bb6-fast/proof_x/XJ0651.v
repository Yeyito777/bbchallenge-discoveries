From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z651 XCuts.b651 XCuts.z652 XCuts.b652 XCuts.n651 XCuts.v651 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
