From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z64 XCuts.b64 XCuts.z65 XCuts.b65 XCuts.n64 XCuts.v64 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
