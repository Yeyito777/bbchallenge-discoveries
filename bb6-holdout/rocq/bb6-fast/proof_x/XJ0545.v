From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z545 XCuts.b545 XCuts.z546 XCuts.b546 XCuts.n545 XCuts.v545 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
