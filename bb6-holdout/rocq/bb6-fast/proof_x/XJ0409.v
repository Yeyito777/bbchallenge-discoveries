From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z409 XCuts.b409 XCuts.z410 XCuts.b410 XCuts.n409 XCuts.v409 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
