From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z222 XCuts.b222 XCuts.z223 XCuts.b223 XCuts.n222 XCuts.v222 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
