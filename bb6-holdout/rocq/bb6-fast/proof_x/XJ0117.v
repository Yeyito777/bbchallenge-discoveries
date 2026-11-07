From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z117 XCuts.b117 XCuts.z118 XCuts.b118 XCuts.n117 XCuts.v117 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
