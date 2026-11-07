From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z476 XCuts.b476 XCuts.z477 XCuts.b477 XCuts.n476 XCuts.v476 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
