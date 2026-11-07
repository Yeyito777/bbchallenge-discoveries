From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z671 XCuts.b671 XCuts.z672 XCuts.b672 XCuts.n671 XCuts.v671 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
