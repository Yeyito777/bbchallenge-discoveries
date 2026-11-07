From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z587 XCuts.b587 XCuts.z588 XCuts.b588 XCuts.n587 XCuts.v587 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
