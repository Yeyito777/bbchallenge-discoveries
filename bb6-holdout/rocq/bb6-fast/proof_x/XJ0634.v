From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z634 XCuts.b634 XCuts.z635 XCuts.b635 XCuts.n634 XCuts.v634 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
