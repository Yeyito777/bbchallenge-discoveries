From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z572 XCuts.b572 XCuts.z573 XCuts.b573 XCuts.n572 XCuts.v572 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
