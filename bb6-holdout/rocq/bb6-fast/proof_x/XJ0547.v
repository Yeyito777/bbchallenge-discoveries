From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z547 XCuts.b547 XCuts.z548 XCuts.b548 XCuts.n547 XCuts.v547 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
