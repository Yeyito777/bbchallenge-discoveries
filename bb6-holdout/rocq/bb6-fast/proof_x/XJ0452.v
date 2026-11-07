From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z452 XCuts.b452 XCuts.z453 XCuts.b453 XCuts.n452 XCuts.v452 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
