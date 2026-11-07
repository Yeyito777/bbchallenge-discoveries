From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z701 XCuts.b701 XCuts.z702 XCuts.b702 XCuts.n701 XCuts.v701 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
