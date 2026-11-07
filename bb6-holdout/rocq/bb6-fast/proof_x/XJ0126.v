From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z126 XCuts.b126 XCuts.z127 XCuts.b127 XCuts.n126 XCuts.v126 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
