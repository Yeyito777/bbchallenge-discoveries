From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z466 XCuts.b466 XCuts.z467 XCuts.b467 XCuts.n466 XCuts.v466 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
