From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z645 XCuts.b645 XCuts.z646 XCuts.b646 XCuts.n645 XCuts.v645 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
