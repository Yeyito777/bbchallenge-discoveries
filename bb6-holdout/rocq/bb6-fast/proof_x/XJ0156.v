From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z156 XCuts.b156 XCuts.z157 XCuts.b157 XCuts.n156 XCuts.v156 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
