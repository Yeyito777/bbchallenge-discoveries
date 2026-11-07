From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z164 XCuts.b164 XCuts.z165 XCuts.b165 XCuts.n164 XCuts.v164 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
