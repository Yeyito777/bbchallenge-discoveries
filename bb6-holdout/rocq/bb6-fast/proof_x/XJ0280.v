From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z280 XCuts.b280 XCuts.z281 XCuts.b281 XCuts.n280 XCuts.v280 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
