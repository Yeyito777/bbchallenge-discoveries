From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z506 XCuts.b506 XCuts.z507 XCuts.b507 XCuts.n506 XCuts.v506 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
