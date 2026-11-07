From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z694 XCuts.b694 XCuts.z695 XCuts.b695 XCuts.n694 XCuts.v694 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
