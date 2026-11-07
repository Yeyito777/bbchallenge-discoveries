From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z335 XCuts.b335 XCuts.z336 XCuts.b336 XCuts.n335 XCuts.v335 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
