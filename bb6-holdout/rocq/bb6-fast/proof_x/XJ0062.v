From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z62 XCuts.b62 XCuts.z63 XCuts.b63 XCuts.n62 XCuts.v62 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
