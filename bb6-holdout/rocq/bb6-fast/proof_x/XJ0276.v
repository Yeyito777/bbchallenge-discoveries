From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z276 XCuts.b276 XCuts.z277 XCuts.b277 XCuts.n276 XCuts.v276 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
