From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z113 XCuts.b113 XCuts.z114 XCuts.b114 XCuts.n113 XCuts.v113 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
