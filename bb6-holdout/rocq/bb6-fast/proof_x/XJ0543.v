From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z543 XCuts.b543 XCuts.z544 XCuts.b544 XCuts.n543 XCuts.v543 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
