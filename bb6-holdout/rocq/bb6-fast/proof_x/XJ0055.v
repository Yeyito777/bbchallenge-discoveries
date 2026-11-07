From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z55 XCuts.b55 XCuts.z56 XCuts.b56 XCuts.n55 XCuts.v55 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
