From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z210 XCuts.b210 XCuts.z211 XCuts.b211 XCuts.n210 XCuts.v210 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
