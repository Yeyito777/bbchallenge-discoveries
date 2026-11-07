From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z403 XCuts.b403 XCuts.z404 XCuts.b404 XCuts.n403 XCuts.v403 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
