From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z67 XCuts.b67 XCuts.z68 XCuts.b68 XCuts.n67 XCuts.v67 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
