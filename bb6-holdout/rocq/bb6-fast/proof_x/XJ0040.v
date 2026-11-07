From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z40 XCuts.b40 XCuts.z41 XCuts.b41 XCuts.n40 XCuts.v40 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
