From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z171 XCuts.b171 XCuts.z172 XCuts.b172 XCuts.n171 XCuts.v171 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
