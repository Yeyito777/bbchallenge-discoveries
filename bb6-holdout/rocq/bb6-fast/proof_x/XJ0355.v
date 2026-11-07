From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z355 XCuts.b355 XCuts.z356 XCuts.b356 XCuts.n355 XCuts.v355 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
