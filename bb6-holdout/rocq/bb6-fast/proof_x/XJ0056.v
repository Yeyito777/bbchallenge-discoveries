From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z56 XCuts.b56 XCuts.z57 XCuts.b57 XCuts.n56 XCuts.v56 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
