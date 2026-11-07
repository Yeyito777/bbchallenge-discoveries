From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z65 XCuts.b65 XCuts.z66 XCuts.b66 XCuts.n65 XCuts.v65 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
