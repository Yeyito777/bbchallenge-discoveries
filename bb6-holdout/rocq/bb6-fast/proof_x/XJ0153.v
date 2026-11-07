From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z153 XCuts.b153 XCuts.z154 XCuts.b154 XCuts.n153 XCuts.v153 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
