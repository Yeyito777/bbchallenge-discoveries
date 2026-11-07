From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z562 XCuts.b562 XCuts.z563 XCuts.b563 XCuts.n562 XCuts.v562 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
