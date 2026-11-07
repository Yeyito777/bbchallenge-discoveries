From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z281 XCuts.b281 XCuts.z282 XCuts.b282 XCuts.n281 XCuts.v281 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
