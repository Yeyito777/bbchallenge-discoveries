From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z693 XCuts.b693 XCuts.z694 XCuts.b694 XCuts.n693 XCuts.v693 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
