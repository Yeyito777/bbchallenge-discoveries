From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z198 XCuts.b198 XCuts.z199 XCuts.b199 XCuts.n198 XCuts.v198 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
