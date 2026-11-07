From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z374 XCuts.b374 XCuts.z375 XCuts.b375 XCuts.n374 XCuts.v374 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
