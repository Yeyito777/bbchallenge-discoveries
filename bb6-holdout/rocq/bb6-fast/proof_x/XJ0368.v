From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z368 XCuts.b368 XCuts.z369 XCuts.b369 XCuts.n368 XCuts.v368 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
