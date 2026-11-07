From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z254 XCuts.b254 XCuts.z255 XCuts.b255 XCuts.n254 XCuts.v254 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
