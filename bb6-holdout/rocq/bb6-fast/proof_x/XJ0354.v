From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z354 XCuts.b354 XCuts.z355 XCuts.b355 XCuts.n354 XCuts.v354 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
