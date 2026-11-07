From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z458 XCuts.b458 XCuts.z459 XCuts.b459 XCuts.n458 XCuts.v458 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
