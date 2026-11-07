From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z628 XCuts.b628 XCuts.z629 XCuts.b629 XCuts.n628 XCuts.v628 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
