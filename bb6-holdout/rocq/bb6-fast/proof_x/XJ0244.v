From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z244 XCuts.b244 XCuts.z245 XCuts.b245 XCuts.n244 XCuts.v244 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
