From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z247 XCuts.b247 XCuts.z248 XCuts.b248 XCuts.n247 XCuts.v247 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
