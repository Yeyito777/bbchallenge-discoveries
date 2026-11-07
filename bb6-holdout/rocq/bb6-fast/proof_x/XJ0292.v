From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z292 XCuts.b292 XCuts.z293 XCuts.b293 XCuts.n292 XCuts.v292 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
