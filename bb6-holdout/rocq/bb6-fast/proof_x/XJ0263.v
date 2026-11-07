From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z263 XCuts.b263 XCuts.z264 XCuts.b264 XCuts.n263 XCuts.v263 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
