From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z558 XCuts.b558 XCuts.z559 XCuts.b559 XCuts.n558 XCuts.v558 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
