From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z475 XCuts.b475 XCuts.z476 XCuts.b476 XCuts.n475 XCuts.v475 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
