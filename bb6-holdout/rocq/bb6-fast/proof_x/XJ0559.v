From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z559 XCuts.b559 XCuts.z560 XCuts.b560 XCuts.n559 XCuts.v559 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
