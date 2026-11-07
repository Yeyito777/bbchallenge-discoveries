From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z273 XCuts.b273 XCuts.z274 XCuts.b274 XCuts.n273 XCuts.v273 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
