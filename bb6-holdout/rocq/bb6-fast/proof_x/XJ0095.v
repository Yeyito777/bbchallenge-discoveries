From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z95 XCuts.b95 XCuts.z96 XCuts.b96 XCuts.n95 XCuts.v95 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
