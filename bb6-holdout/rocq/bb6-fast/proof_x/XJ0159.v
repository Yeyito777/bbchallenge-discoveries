From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z159 XCuts.b159 XCuts.z160 XCuts.b160 XCuts.n159 XCuts.v159 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
