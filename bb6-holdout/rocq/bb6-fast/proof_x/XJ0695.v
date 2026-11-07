From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z695 XCuts.b695 XCuts.z696 XCuts.b696 XCuts.n695 XCuts.v695 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
