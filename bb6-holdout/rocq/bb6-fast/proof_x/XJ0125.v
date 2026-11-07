From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z125 XCuts.b125 XCuts.z126 XCuts.b126 XCuts.n125 XCuts.v125 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
