From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z163 XCuts.b163 XCuts.z164 XCuts.b164 XCuts.n163 XCuts.v163 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
