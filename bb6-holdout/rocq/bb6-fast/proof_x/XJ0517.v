From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z517 XCuts.b517 XCuts.z518 XCuts.b518 XCuts.n517 XCuts.v517 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
