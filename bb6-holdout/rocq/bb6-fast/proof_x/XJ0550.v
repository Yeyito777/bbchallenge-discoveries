From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z550 XCuts.b550 XCuts.z551 XCuts.b551 XCuts.n550 XCuts.v550 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
