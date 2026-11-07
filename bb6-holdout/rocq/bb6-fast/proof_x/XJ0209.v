From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z209 XCuts.b209 XCuts.z210 XCuts.b210 XCuts.n209 XCuts.v209 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
