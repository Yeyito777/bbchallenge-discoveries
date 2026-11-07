From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z120 XCuts.b120 XCuts.z121 XCuts.b121 XCuts.n120 XCuts.v120 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
