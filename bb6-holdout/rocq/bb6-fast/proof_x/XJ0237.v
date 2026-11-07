From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z237 XCuts.b237 XCuts.z238 XCuts.b238 XCuts.n237 XCuts.v237 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
