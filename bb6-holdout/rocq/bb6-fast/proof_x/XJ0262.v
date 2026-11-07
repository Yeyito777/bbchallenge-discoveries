From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z262 XCuts.b262 XCuts.z263 XCuts.b263 XCuts.n262 XCuts.v262 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
