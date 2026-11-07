From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z509 XCuts.b509 XCuts.z510 XCuts.b510 XCuts.n509 XCuts.v509 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
