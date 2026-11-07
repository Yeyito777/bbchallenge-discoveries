From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z236 XCuts.b236 XCuts.z237 XCuts.b237 XCuts.n236 XCuts.v236 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
