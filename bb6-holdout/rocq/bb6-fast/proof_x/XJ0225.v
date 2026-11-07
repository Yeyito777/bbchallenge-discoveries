From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z225 XCuts.b225 XCuts.z226 XCuts.b226 XCuts.n225 XCuts.v225 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
