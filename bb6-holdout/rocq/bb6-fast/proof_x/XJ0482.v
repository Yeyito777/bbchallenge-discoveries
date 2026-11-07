From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z482 XCuts.b482 XCuts.z483 XCuts.b483 XCuts.n482 XCuts.v482 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
