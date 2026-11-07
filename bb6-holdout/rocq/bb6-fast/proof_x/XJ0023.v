From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z23 XCuts.b23 XCuts.z24 XCuts.b24 XCuts.n23 XCuts.v23 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
