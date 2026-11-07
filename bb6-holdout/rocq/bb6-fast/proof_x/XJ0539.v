From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z539 XCuts.b539 XCuts.z540 XCuts.b540 XCuts.n539 XCuts.v539 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
