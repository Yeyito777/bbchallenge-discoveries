From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z703 XCuts.b703 XCuts.z704 XCuts.b704 XCuts.n703 XCuts.v703 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
