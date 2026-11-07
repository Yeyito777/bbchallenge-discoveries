From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z500 XCuts.b500 XCuts.z501 XCuts.b501 XCuts.n500 XCuts.v500 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
