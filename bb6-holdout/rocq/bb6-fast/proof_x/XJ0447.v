From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z447 XCuts.b447 XCuts.z448 XCuts.b448 XCuts.n447 XCuts.v447 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
