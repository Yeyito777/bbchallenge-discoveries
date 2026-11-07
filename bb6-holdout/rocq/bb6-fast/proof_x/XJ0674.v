From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z674 XCuts.b674 XCuts.z675 XCuts.b675 XCuts.n674 XCuts.v674 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
