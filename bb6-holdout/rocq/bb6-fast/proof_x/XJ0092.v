From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z92 XCuts.b92 XCuts.z93 XCuts.b93 XCuts.n92 XCuts.v92 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
