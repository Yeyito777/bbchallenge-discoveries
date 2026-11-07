From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z181 XCuts.b181 XCuts.z182 XCuts.b182 XCuts.n181 XCuts.v181 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
