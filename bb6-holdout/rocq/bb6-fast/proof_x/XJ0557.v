From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z557 XCuts.b557 XCuts.z558 XCuts.b558 XCuts.n557 XCuts.v557 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
