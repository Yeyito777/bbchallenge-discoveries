From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z305 XCuts.b305 XCuts.z306 XCuts.b306 XCuts.n305 XCuts.v305 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
