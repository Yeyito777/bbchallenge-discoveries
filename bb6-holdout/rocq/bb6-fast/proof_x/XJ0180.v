From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z180 XCuts.b180 XCuts.z181 XCuts.b181 XCuts.n180 XCuts.v180 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
