From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z110 XCuts.b110 XCuts.z111 XCuts.b111 XCuts.n110 XCuts.v110 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
