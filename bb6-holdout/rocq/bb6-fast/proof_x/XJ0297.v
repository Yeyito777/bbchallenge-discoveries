From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z297 XCuts.b297 XCuts.z298 XCuts.b298 XCuts.n297 XCuts.v297 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
