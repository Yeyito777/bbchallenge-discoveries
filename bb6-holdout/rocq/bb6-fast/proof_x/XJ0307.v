From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z307 XCuts.b307 XCuts.z308 XCuts.b308 XCuts.n307 XCuts.v307 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
