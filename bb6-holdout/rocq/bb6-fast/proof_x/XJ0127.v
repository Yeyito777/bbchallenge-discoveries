From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z127 XCuts.b127 XCuts.z128 XCuts.b128 XCuts.n127 XCuts.v127 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
