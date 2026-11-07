From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z301 XCuts.b301 XCuts.z302 XCuts.b302 XCuts.n301 XCuts.v301 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
