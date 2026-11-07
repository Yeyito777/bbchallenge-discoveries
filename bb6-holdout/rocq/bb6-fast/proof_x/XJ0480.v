From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z480 XCuts.b480 XCuts.z481 XCuts.b481 XCuts.n480 XCuts.v480 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
