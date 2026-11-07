From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z443 XCuts.b443 XCuts.z444 XCuts.b444 XCuts.n443 XCuts.v443 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
