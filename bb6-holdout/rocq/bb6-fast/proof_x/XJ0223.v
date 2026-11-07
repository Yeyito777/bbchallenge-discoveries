From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z223 XCuts.b223 XCuts.z224 XCuts.b224 XCuts.n223 XCuts.v223 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
