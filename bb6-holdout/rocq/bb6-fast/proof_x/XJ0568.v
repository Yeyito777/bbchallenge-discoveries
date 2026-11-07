From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z568 XCuts.b568 XCuts.z569 XCuts.b569 XCuts.n568 XCuts.v568 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
