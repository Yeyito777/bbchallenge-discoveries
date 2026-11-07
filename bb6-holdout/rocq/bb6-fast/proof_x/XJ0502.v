From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z502 XCuts.b502 XCuts.z503 XCuts.b503 XCuts.n502 XCuts.v502 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
