From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z567 XCuts.b567 XCuts.z568 XCuts.b568 XCuts.n567 XCuts.v567 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
