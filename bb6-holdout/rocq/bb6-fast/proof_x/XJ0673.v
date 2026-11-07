From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z673 XCuts.b673 XCuts.z674 XCuts.b674 XCuts.n673 XCuts.v673 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
