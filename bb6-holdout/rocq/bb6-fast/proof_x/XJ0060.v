From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z60 XCuts.b60 XCuts.z61 XCuts.b61 XCuts.n60 XCuts.v60 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
