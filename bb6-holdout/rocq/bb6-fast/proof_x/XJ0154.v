From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z154 XCuts.b154 XCuts.z155 XCuts.b155 XCuts.n154 XCuts.v154 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
