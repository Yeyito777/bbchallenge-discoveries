From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z162 XCuts.b162 XCuts.z163 XCuts.b163 XCuts.n162 XCuts.v162 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
