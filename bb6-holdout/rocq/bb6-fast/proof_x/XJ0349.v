From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z349 XCuts.b349 XCuts.z350 XCuts.b350 XCuts.n349 XCuts.v349 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
