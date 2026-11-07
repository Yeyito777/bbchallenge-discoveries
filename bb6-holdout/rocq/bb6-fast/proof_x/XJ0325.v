From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z325 XCuts.b325 XCuts.z326 XCuts.b326 XCuts.n325 XCuts.v325 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
