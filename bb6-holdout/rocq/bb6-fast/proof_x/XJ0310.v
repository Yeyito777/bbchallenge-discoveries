From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z310 XCuts.b310 XCuts.z311 XCuts.b311 XCuts.n310 XCuts.v310 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
