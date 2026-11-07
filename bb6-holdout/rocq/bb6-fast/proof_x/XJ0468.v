From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z468 XCuts.b468 XCuts.z469 XCuts.b469 XCuts.n468 XCuts.v468 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
