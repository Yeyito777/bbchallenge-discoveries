From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z25 XCuts.b25 XCuts.z26 XCuts.b26 XCuts.n25 XCuts.v25 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
