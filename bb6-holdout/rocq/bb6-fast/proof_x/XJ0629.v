From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z629 XCuts.b629 XCuts.z630 XCuts.b630 XCuts.n629 XCuts.v629 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
