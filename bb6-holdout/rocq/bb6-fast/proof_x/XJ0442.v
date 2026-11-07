From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z442 XCuts.b442 XCuts.z443 XCuts.b443 XCuts.n442 XCuts.v442 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
