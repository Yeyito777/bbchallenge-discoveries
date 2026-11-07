From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z577 XCuts.b577 XCuts.z578 XCuts.b578 XCuts.n577 XCuts.v577 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
