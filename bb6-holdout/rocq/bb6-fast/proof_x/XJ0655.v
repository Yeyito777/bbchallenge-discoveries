From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z655 XCuts.b655 XCuts.z656 XCuts.b656 XCuts.n655 XCuts.v655 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
