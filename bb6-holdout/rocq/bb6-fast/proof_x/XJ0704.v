From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z704 XCuts.b704 XCuts.z705 XCuts.b705 XCuts.n704 XCuts.v704 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
