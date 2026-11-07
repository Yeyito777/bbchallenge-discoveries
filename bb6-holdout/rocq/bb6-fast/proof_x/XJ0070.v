From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z70 XCuts.b70 XCuts.z71 XCuts.b71 XCuts.n70 XCuts.v70 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
