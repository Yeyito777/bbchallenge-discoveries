From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z624 XCuts.b624 XCuts.z625 XCuts.b625 XCuts.n624 XCuts.v624 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
