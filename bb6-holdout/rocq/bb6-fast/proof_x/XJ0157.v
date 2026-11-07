From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z157 XCuts.b157 XCuts.z158 XCuts.b158 XCuts.n157 XCuts.v157 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
