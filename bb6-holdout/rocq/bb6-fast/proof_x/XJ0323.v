From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z323 XCuts.b323 XCuts.z324 XCuts.b324 XCuts.n323 XCuts.v323 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
