From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z340 XCuts.b340 XCuts.z341 XCuts.b341 XCuts.n340 XCuts.v340 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
