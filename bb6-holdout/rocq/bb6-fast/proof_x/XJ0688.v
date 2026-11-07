From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z688 XCuts.b688 XCuts.z689 XCuts.b689 XCuts.n688 XCuts.v688 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
