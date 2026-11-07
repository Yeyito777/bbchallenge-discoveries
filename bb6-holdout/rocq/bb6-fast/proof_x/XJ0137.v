From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z137 XCuts.b137 XCuts.z138 XCuts.b138 XCuts.n137 XCuts.v137 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
