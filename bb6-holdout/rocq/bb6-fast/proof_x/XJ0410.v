From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z410 XCuts.b410 XCuts.z411 XCuts.b411 XCuts.n410 XCuts.v410 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
