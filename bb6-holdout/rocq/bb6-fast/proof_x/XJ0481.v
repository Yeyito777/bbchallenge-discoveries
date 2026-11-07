From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z481 XCuts.b481 XCuts.z482 XCuts.b482 XCuts.n481 XCuts.v481 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
