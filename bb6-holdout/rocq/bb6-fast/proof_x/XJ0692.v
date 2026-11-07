From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z692 XCuts.b692 XCuts.z693 XCuts.b693 XCuts.n692 XCuts.v692 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
