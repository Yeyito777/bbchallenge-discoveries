From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z555 XCuts.b555 XCuts.z556 XCuts.b556 XCuts.n555 XCuts.v555 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
