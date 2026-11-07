From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z218 XCuts.b218 XCuts.z219 XCuts.b219 XCuts.n218 XCuts.v218 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
