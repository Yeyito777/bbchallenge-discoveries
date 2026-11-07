From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z519 XCuts.b519 XCuts.z520 XCuts.b520 XCuts.n519 XCuts.v519 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
