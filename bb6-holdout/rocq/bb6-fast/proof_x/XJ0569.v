From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z569 XCuts.b569 XCuts.z570 XCuts.b570 XCuts.n569 XCuts.v569 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
