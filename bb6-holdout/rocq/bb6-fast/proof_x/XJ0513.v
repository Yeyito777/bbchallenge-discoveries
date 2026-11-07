From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z513 XCuts.b513 XCuts.z514 XCuts.b514 XCuts.n513 XCuts.v513 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
