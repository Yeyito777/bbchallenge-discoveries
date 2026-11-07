From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z542 XCuts.b542 XCuts.z543 XCuts.b543 XCuts.n542 XCuts.v542 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
