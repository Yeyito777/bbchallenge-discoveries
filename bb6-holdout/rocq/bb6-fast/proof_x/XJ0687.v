From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z687 XCuts.b687 XCuts.z688 XCuts.b688 XCuts.n687 XCuts.v687 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
