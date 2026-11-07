From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z89 XCuts.b89 XCuts.z90 XCuts.b90 XCuts.n89 XCuts.v89 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
