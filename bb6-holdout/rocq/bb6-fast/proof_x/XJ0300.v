From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z300 XCuts.b300 XCuts.z301 XCuts.b301 XCuts.n300 XCuts.v300 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
