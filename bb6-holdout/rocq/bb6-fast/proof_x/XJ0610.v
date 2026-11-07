From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z610 XCuts.b610 XCuts.z611 XCuts.b611 XCuts.n610 XCuts.v610 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
