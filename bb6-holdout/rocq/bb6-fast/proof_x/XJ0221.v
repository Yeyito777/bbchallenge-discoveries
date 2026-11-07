From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z221 XCuts.b221 XCuts.z222 XCuts.b222 XCuts.n221 XCuts.v221 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
