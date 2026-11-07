From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z203 XCuts.b203 XCuts.z204 XCuts.b204 XCuts.n203 XCuts.v203 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
