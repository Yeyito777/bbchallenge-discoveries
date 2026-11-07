From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z195 XCuts.b195 XCuts.z196 XCuts.b196 XCuts.n195 XCuts.v195 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
