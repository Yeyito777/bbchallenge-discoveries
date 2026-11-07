From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z535 XCuts.b535 XCuts.z536 XCuts.b536 XCuts.n535 XCuts.v535 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
