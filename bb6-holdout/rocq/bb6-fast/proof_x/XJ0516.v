From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z516 XCuts.b516 XCuts.z517 XCuts.b517 XCuts.n516 XCuts.v516 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
