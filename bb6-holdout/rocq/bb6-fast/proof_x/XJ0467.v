From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z467 XCuts.b467 XCuts.z468 XCuts.b468 XCuts.n467 XCuts.v467 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
