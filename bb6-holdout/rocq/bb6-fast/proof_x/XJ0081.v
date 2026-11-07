From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z81 XCuts.b81 XCuts.z82 XCuts.b82 XCuts.n81 XCuts.v81 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
