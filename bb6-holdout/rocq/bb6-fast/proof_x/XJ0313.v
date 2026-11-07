From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z313 XCuts.b313 XCuts.z314 XCuts.b314 XCuts.n313 XCuts.v313 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
