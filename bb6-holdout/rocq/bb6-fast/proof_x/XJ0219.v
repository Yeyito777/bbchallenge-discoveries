From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z219 XCuts.b219 XCuts.z220 XCuts.b220 XCuts.n219 XCuts.v219 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
