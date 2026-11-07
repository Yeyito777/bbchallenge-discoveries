From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z302 XCuts.b302 XCuts.z303 XCuts.b303 XCuts.n302 XCuts.v302 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
