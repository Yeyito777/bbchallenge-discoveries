From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z596 XCuts.b596 XCuts.z597 XCuts.b597 XCuts.n596 XCuts.v596 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
