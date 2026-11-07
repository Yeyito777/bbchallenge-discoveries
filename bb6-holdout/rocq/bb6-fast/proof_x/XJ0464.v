From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z464 XCuts.b464 XCuts.z465 XCuts.b465 XCuts.n464 XCuts.v464 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
