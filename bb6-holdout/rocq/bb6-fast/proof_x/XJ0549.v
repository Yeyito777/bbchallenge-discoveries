From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z549 XCuts.b549 XCuts.z550 XCuts.b550 XCuts.n549 XCuts.v549 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
