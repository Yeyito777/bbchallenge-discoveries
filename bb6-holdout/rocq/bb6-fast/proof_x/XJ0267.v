From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z267 XCuts.b267 XCuts.z268 XCuts.b268 XCuts.n267 XCuts.v267 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
