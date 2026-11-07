From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z48 XCuts.b48 XCuts.z49 XCuts.b49 XCuts.n48 XCuts.v48 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
