From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z609 XCuts.b609 XCuts.z610 XCuts.b610 XCuts.n609 XCuts.v609 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
