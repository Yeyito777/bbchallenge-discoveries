From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z204 XCuts.b204 XCuts.z205 XCuts.b205 XCuts.n204 XCuts.v204 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
