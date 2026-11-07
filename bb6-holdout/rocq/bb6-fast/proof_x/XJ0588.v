From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z588 XCuts.b588 XCuts.z589 XCuts.b589 XCuts.n588 XCuts.v588 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
