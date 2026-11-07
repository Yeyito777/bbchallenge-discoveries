From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z66 XCuts.b66 XCuts.z67 XCuts.b67 XCuts.n66 XCuts.v66 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
