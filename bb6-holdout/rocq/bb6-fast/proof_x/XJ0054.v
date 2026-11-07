From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z54 XCuts.b54 XCuts.z55 XCuts.b55 XCuts.n54 XCuts.v54 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
