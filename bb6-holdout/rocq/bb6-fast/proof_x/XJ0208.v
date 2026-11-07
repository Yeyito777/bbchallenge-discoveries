From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z208 XCuts.b208 XCuts.z209 XCuts.b209 XCuts.n208 XCuts.v208 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
