From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z492 XCuts.b492 XCuts.z493 XCuts.b493 XCuts.n492 XCuts.v492 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
