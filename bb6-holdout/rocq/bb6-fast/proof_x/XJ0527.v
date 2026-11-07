From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z527 XCuts.b527 XCuts.z528 XCuts.b528 XCuts.n527 XCuts.v527 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
