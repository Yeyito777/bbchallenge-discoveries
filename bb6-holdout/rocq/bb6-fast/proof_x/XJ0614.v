From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z614 XCuts.b614 XCuts.z615 XCuts.b615 XCuts.n614 XCuts.v614 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
