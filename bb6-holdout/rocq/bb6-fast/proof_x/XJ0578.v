From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z578 XCuts.b578 XCuts.z579 XCuts.b579 XCuts.n578 XCuts.v578 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
