From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z434 XCuts.b434 XCuts.z435 XCuts.b435 XCuts.n434 XCuts.v434 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
