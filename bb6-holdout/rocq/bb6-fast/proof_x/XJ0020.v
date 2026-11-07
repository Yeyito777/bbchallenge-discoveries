From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z20 XCuts.b20 XCuts.z21 XCuts.b21 XCuts.n20 XCuts.v20 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
