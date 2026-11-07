From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z211 XCuts.b211 XCuts.z212 XCuts.b212 XCuts.n211 XCuts.v211 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
