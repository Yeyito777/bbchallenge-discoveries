From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z474 XCuts.b474 XCuts.z475 XCuts.b475 XCuts.n474 XCuts.v474 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
