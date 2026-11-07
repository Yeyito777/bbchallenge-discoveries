From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z446 XCuts.b446 XCuts.z447 XCuts.b447 XCuts.n446 XCuts.v446 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
