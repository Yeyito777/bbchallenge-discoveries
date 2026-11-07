From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z255 XCuts.b255 XCuts.z256 XCuts.b256 XCuts.n255 XCuts.v255 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
